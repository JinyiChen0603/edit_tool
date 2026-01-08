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

