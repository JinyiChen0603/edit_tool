from flask import Flask, render_template, request, jsonify
import os
import re
from pathlib import Path

app = Flask(__name__)
MATHS_DIR = Path('Maths')

class Question:
    def __init__(self, filepath):
        self.filepath = filepath
        self.content = self.read_file()
        self.parse()
    
    def read_file(self):
        with open(self.filepath, 'r', encoding='utf-8') as f:
            return f.read()
    
    def parse(self):
        """解析markdown文件"""
        # 解析YAML头部
        yaml_match = re.match(r'^---\n(.*?)\n---\n', self.content, re.DOTALL)
        if yaml_match:
            yaml_content = yaml_match.group(1)
            self.metadata = {}
            for line in yaml_content.split('\n'):
                if ':' in line:
                    key, value = line.split(':', 1)
                    self.metadata[key.strip()] = value.strip()
            
            # 解析内容部分
            rest_content = self.content[yaml_match.end():]
            
            # 提取题目
            question_match = re.search(r'## 题目\n(.*?)(?=\n## )', rest_content, re.DOTALL)
            self.question = question_match.group(1).strip() if question_match else ""
            
            # 提取解答
            answer_match = re.search(r'## 解答\n(.*?)(?=\n## )', rest_content, re.DOTALL)
            self.solution = answer_match.group(1).strip() if answer_match else ""
            
            # 提取答案
            final_answer_match = re.search(r'## 答案\n(.*?)$', rest_content, re.DOTALL)
            self.answer = final_answer_match.group(1).strip() if final_answer_match else ""
    
    def to_dict(self):
        return {
            'filepath': str(self.filepath),
            'filename': self.filepath.name,
            'metadata': self.metadata,
            'question': self.question,
            'solution': self.solution,
            'answer': self.answer,
            'marked': self.metadata.get('marked', 'false').lower() == 'true'
        }
    
    def save(self, metadata, question, solution, answer):
        """保存修改"""
        yaml_lines = ['---']
        for key, value in metadata.items():
            yaml_lines.append(f'{key}: {value}')
        yaml_lines.append('---')
        
        new_content = '\n'.join(yaml_lines)
        new_content += f'\n\n## 题目\n{question}\n\n## 解答\n{solution}\n\n## 答案\n{answer}\n'
        
        with open(self.filepath, 'w', encoding='utf-8') as f:
            f.write(new_content)

def get_all_questions():
    """获取所有题目"""
    questions = []
    for md_file in sorted(MATHS_DIR.glob('q_*.md')):
        try:
            q = Question(md_file)
            questions.append(q.to_dict())
        except Exception as e:
            print(f"Error reading {md_file}: {e}")
    return questions

@app.route('/')
def index():
    return render_template('index.html')

@app.route('/api/questions', methods=['GET'])
def list_questions():
    """列出所有题目"""
    questions = get_all_questions()
    return jsonify(questions)

@app.route('/api/search', methods=['GET'])
def search_questions():
    """搜索题目"""
    query = request.args.get('q', '').lower()
    questions = get_all_questions()
    
    if not query:
        return jsonify(questions)
    
    # 定义要搜索的字段
    search_fields = ['id', 'title', 'question_type', 'difficulty', 
                     'domain', 'knowledge_point', 'teacher']
    
    results = []
    for q in questions:
        # 在元数据字段中搜索
        for field in search_fields:
            if query in q['metadata'].get(field, '').lower():
                results.append(q)
                break
        else:
            # 如果元数据中没找到，搜索题目内容
            if query in q['question'].lower():
                results.append(q)
    
    return jsonify(results)

@app.route('/api/question/<filename>', methods=['GET'])
def get_question(filename):
    """获取单个题目详情"""
    filepath = MATHS_DIR / filename
    if not filepath.exists():
        return jsonify({'error': 'File not found'}), 404
    
    q = Question(filepath)
    return jsonify(q.to_dict())

@app.route('/api/question/<filename>', methods=['PUT'])
def update_question(filename):
    """更新题目"""
    filepath = MATHS_DIR / filename
    if not filepath.exists():
        return jsonify({'error': 'File not found'}), 404
    
    data = request.json
    q = Question(filepath)
    
    try:
        q.save(
            metadata=data['metadata'],
            question=data['question'],
            solution=data['solution'],
            answer=data['answer']
        )
        return jsonify({'success': True, 'message': '保存成功'})
    except Exception as e:
        return jsonify({'success': False, 'error': str(e)}), 500

@app.route('/api/marked', methods=['GET'])
def list_marked():
    """列出所有标记的题目"""
    questions = get_all_questions()
    marked = [q for q in questions if q.get('marked', False)]
    return jsonify(marked)

@app.route('/api/question/<filename>/toggle-mark', methods=['POST'])
def toggle_mark(filename):
    """切换题目标记状态"""
    filepath = MATHS_DIR / filename
    if not filepath.exists():
        return jsonify({'error': 'File not found'}), 404
    
    q = Question(filepath)
    current_marked = q.metadata.get('marked', 'false').lower() == 'true'
    q.metadata['marked'] = 'false' if current_marked else 'true'
    
    q.save(
        metadata=q.metadata,
        question=q.question,
        solution=q.solution,
        answer=q.answer
    )
    
    return jsonify({'success': True, 'marked': not current_marked})

@app.route('/api/question/create', methods=['POST'])
def create_question():
    """创建新题目"""
    try:
        # 获取下一个可用的ID
        existing_ids = []
        for md_file in MATHS_DIR.glob('q_*.md'):
            match = re.match(r'q_(\d+)\.md', md_file.name)
            if match:
                existing_ids.append(int(match.group(1)))
        
        next_id = max(existing_ids) + 1 if existing_ids else 1
        
        # 创建新文件名
        new_filename = f'q_{next_id}.md'
        new_filepath = MATHS_DIR / new_filename
        
        # 检查文件是否已存在
        if new_filepath.exists():
            return jsonify({'error': '文件已存在'}), 400
        
        # 创建默认内容
        default_content = f"""---
id: {next_id}
title: 
question_type: 
domain: 
difficulty: 
knowledge_point: 
batch: 
teacher: 
marked: false
---

## 题目


## 解答


## 答案

"""
        
        # 写入文件
        with open(new_filepath, 'w', encoding='utf-8') as f:
            f.write(default_content)
        
        return jsonify({
            'success': True,
            'filename': new_filename,
            'id': next_id,
            'message': f'成功创建题目 {next_id}'
        })
    
    except Exception as e:
        return jsonify({'success': False, 'error': str(e)}), 500

@app.route('/api/question/<filename>', methods=['DELETE'])
def delete_question(filename):
    """删除题目"""
    filepath = MATHS_DIR / filename
    if not filepath.exists():
        return jsonify({'error': '文件不存在'}), 404
    
    try:
        # 获取题目ID用于显示
        q = Question(filepath)
        question_id = q.metadata.get('id', filename)
        
        # 删除文件
        filepath.unlink()
        
        return jsonify({
            'success': True,
            'message': f'成功删除题目 {question_id}'
        })
    except Exception as e:
        return jsonify({'success': False, 'error': str(e)}), 500

@app.route('/api/question/import', methods=['POST'])
def import_question():
    """导入题目（支持多种格式）"""
    try:
        data = request.json
        content = data.get('content', '')
        
        if not content:
            return jsonify({'error': '导入内容为空'}), 400
        
        # 预处理：统一换行符，去除BOM
        content = content.replace('\r\n', '\n').replace('\r', '\n')
        # 去除UTF-8 BOM
        if content.startswith('\ufeff'):
            content = content[1:]
        content = content.strip()
        
        # 获取下一个可用的ID
        existing_ids = []
        for md_file in MATHS_DIR.glob('q_*.md'):
            match = re.match(r'q_(\d+)\.md', md_file.name)
            if match:
                existing_ids.append(int(match.group(1)))
        
        next_id = max(existing_ids) + 1 if existing_ids else 1
        
        # 初始化变量
        metadata = {
            'id': str(next_id),
            'title': '',
            'question_type': '',
            'domain': '',
            'difficulty': '',
            'knowledge_point': '',
            'batch': '',
            'teacher': '',
            'marked': 'false'
        }
        question = ""
        solution = ""
        answer = ""
        has_yaml = False
        
        # 尝试解析不同格式
        try:
            # 改进的YAML匹配：允许分隔符前后有空格
            yaml_match = re.match(r'^\s*---\s*\n(.*?)\n\s*---\s*\n', content, re.DOTALL)
            if not yaml_match:
                # 如果还是匹配不到，尝试更宽松的匹配
                yaml_match = re.search(r'---\s*\n(.*?)\n\s*---', content, re.DOTALL)
            
            if yaml_match:
                # 标准格式：有YAML头部
                has_yaml = True
                yaml_content = yaml_match.group(1)
                parsed_metadata = {}
                for line in yaml_content.split('\n'):
                    if ':' in line:
                        key, value = line.split(':', 1)
                        parsed_metadata[key.strip()] = value.strip()
                
                # 更新元数据（保留默认值作为后备）
                for key in metadata.keys():
                    if key != 'id' and key in parsed_metadata:
                        metadata[key] = parsed_metadata[key]
                
                # 提取内容部分
                rest_content = content[yaml_match.end():]
                
                # 提取题目（允许章节标题前后有空格）
                question_match = re.search(r'##\s*题目\s*\n(.*?)(?=\n\s*##\s*|$)', rest_content, re.DOTALL)
                if question_match:
                    question = question_match.group(1).strip()
                
                # 提取解答
                solution_match = re.search(r'##\s*解答\s*\n(.*?)(?=\n\s*##\s*|$)', rest_content, re.DOTALL)
                if solution_match:
                    solution = solution_match.group(1).strip()
                
                # 提取答案
                answer_match = re.search(r'##\s*答案\s*\n(.*?)$', rest_content, re.DOTALL)
                if answer_match:
                    answer = answer_match.group(1).strip()
                    
            else:
                # 无YAML头部：智能识别
                # 尝试识别标题（第一行或第一个#标题）
                lines = content.strip().split('\n')
                first_line = lines[0] if lines else ''
                
                # 尝试从第一行提取标题
                if first_line.startswith('#'):
                    metadata['title'] = first_line.lstrip('#').strip()
                    content = '\n'.join(lines[1:])
                
                # 尝试识别章节
                if '## 题目' in content or '##题目' in content:
                    # 有章节标记但没有YAML
                    question_match = re.search(r'##\s*题目\s*\n(.*?)(?=\n\s*##\s*|$)', content, re.DOTALL)
                    if question_match:
                        question = question_match.group(1).strip()
                    
                    solution_match = re.search(r'##\s*解答\s*\n(.*?)(?=\n\s*##\s*|$)', content, re.DOTALL)
                    if solution_match:
                        solution = solution_match.group(1).strip()
                    
                    answer_match = re.search(r'##\s*答案\s*\n(.*?)$', content, re.DOTALL)
                    if answer_match:
                        answer = answer_match.group(1).strip()
                    
                    if not metadata['title']:
                        metadata['title'] = '导入的题目（需手动整理）'
                else:
                    # 完全自由格式：全部放入题目部分
                    question = content.strip()
                    metadata['title'] = '导入的题目（需手动整理）'
                    
        except Exception as e:
            # 解析失败，使用手动模式
            question = content.strip()
            metadata['title'] = '导入的题目（解析失败，需手动整理）'
        
        # 创建新文件
        new_filename = f'q_{next_id}.md'
        new_filepath = MATHS_DIR / new_filename
        
        if new_filepath.exists():
            return jsonify({'error': '文件已存在'}), 400
        
        # 构建新内容
        yaml_lines = ['---']
        for key, value in metadata.items():
            yaml_lines.append(f'{key}: {value}')
        yaml_lines.append('---')
        
        new_content = '\n'.join(yaml_lines)
        new_content += f'\n\n## 题目\n{question}\n\n## 解答\n{solution}\n\n## 答案\n{answer}\n'
        
        # 写入文件
        with open(new_filepath, 'w', encoding='utf-8') as f:
            f.write(new_content)
        
        return jsonify({
            'success': True,
            'filename': new_filename,
            'id': next_id,
            'message': f'成功导入题目 {next_id}',
            'warning': '请检查并完善题目信息' if not has_yaml else None
        })
    
    except Exception as e:
        return jsonify({'success': False, 'error': str(e)}), 500

if __name__ == '__main__':
    # host='0.0.0.0' 允许局域网访问
    # port=5000 端口号
    print("=" * 60)
    print("数学题目编辑器已启动！")
    print("=" * 60)
    print("本地访问地址: http://localhost:5000")
    print("局域网访问: 请在其他设备上使用你的局域网IP访问")
    print("获取IP地址: 在命令行运行 ipconfig 查看 IPv4 地址")
    print("例如: http://192.168.1.100:5000")
    print("=" * 60)
    app.run(host='0.0.0.0', port=5000, debug=True)

