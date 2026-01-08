import tkinter as tk
from tkinter import ttk, messagebox, scrolledtext
import os
import re
from pathlib import Path

class QuestionEditor:
    def __init__(self, root):
        self.root = root
        self.root.title("数学题目编辑器")
        self.root.geometry("1200x800")
        
        self.maths_dir = Path('maths')
        self.current_file = None
        self.questions = []
        
        self.setup_ui()
        self.load_questions()
    
    def setup_ui(self):
        # 创建主容器
        main_container = tk.PanedWindow(self.root, orient=tk.HORIZONTAL)
        main_container.pack(fill=tk.BOTH, expand=True)
        
        # 左侧面板：搜索和列表
        left_panel = tk.Frame(main_container, width=300)
        main_container.add(left_panel)
        
        # 搜索框
        search_frame = tk.Frame(left_panel)
        search_frame.pack(fill=tk.X, padx=10, pady=10)
        
        tk.Label(search_frame, text="搜索:", font=("微软雅黑", 10)).pack(side=tk.LEFT)
        self.search_var = tk.StringVar()
        self.search_var.trace('w', lambda *args: self.filter_questions())
        search_entry = tk.Entry(search_frame, textvariable=self.search_var)
        search_entry.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=5)
        
        # 题目列表
        list_frame = tk.Frame(left_panel)
        list_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=(0, 10))
        
        scrollbar = tk.Scrollbar(list_frame)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        
        self.question_listbox = tk.Listbox(
            list_frame, 
            yscrollcommand=scrollbar.set,
            font=("微软雅黑", 10),
            height=30
        )
        self.question_listbox.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        scrollbar.config(command=self.question_listbox.yview)
        self.question_listbox.bind('<<ListboxSelect>>', self.on_question_select)
        
        # 右侧面板：编辑器
        right_panel = tk.Frame(main_container)
        main_container.add(right_panel)
        
        # 顶部：标题和保存按钮
        top_frame = tk.Frame(right_panel)
        top_frame.pack(fill=tk.X, padx=10, pady=10)
        
        self.title_label = tk.Label(
            top_frame, 
            text="请从左侧选择题目", 
            font=("微软雅黑", 14, "bold")
        )
        self.title_label.pack(side=tk.LEFT)
        
        self.save_btn = tk.Button(
            top_frame,
            text="保存修改 (Ctrl+S)",
            command=self.save_question,
            bg="#1976d2",
            fg="white",
            font=("微软雅黑", 10, "bold"),
            padx=20,
            pady=5,
            state=tk.DISABLED
        )
        self.save_btn.pack(side=tk.RIGHT)
        
        # 编辑区域
        edit_frame = tk.Frame(right_panel)
        edit_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=(0, 10))
        
        # 使用Canvas和Scrollbar创建可滚动区域
        canvas = tk.Canvas(edit_frame)
        scrollbar = tk.Scrollbar(edit_frame, orient="vertical", command=canvas.yview)
        self.scrollable_frame = tk.Frame(canvas)
        
        self.scrollable_frame.bind(
            "<Configure>",
            lambda e: canvas.configure(scrollregion=canvas.bbox("all"))
        )
        
        canvas.create_window((0, 0), window=self.scrollable_frame, anchor="nw")
        canvas.configure(yscrollcommand=scrollbar.set)
        
        canvas.pack(side="left", fill="both", expand=True)
        scrollbar.pack(side="right", fill="y")
        
        # 元数据字段
        metadata_frame = tk.LabelFrame(
            self.scrollable_frame, 
            text="元数据", 
            font=("微软雅黑", 10, "bold"),
            padx=10,
            pady=10
        )
        metadata_frame.pack(fill=tk.X, pady=(0, 10))
        
        # 创建两列布局
        left_col = tk.Frame(metadata_frame)
        left_col.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(0, 10))
        
        right_col = tk.Frame(metadata_frame)
        right_col.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        
        # 元数据输入框
        self.meta_fields = {}
        meta_labels = [
            ("ID", "id", left_col),
            ("标题", "title", left_col),
            ("题型", "question_type", left_col),
            ("领域", "domain", right_col),
            ("难度", "difficulty", right_col),
            ("知识点", "knowledge_point", right_col)
        ]
        
        for label_text, field_name, parent in meta_labels:
            frame = tk.Frame(parent)
            frame.pack(fill=tk.X, pady=5)
            tk.Label(frame, text=label_text + ":", width=8, anchor='w').pack(side=tk.LEFT)
            entry = tk.Entry(frame, font=("微软雅黑", 10))
            entry.pack(side=tk.LEFT, fill=tk.X, expand=True)
            self.meta_fields[field_name] = entry
            if field_name == "id":
                entry.config(state='readonly')
        
        # 题目内容
        self.create_text_field(
            self.scrollable_frame, 
            "题目内容", 
            "question_text", 
            height=8
        )
        
        # 解答过程
        self.create_text_field(
            self.scrollable_frame, 
            "解答过程", 
            "solution_text", 
            height=15
        )
        
        # 最终答案
        self.create_text_field(
            self.scrollable_frame, 
            "最终答案", 
            "answer_text", 
            height=4
        )
        
        # 绑定快捷键
        self.root.bind('<Control-s>', lambda e: self.save_question())
        
        # 绑定鼠标滚轮
        canvas.bind_all("<MouseWheel>", lambda e: canvas.yview_scroll(int(-1*(e.delta/120)), "units"))
    
    def create_text_field(self, parent, label, field_name, height=10):
        frame = tk.LabelFrame(
            parent, 
            text=label, 
            font=("微软雅黑", 10, "bold"),
            padx=10,
            pady=10
        )
        frame.pack(fill=tk.BOTH, expand=True, pady=(0, 10))
        
        text_widget = scrolledtext.ScrolledText(
            frame,
            font=("Consolas", 10),
            height=height,
            wrap=tk.WORD
        )
        text_widget.pack(fill=tk.BOTH, expand=True)
        
        self.meta_fields[field_name] = text_widget
    
    def load_questions(self):
        """加载所有题目"""
        self.questions = []
        if not self.maths_dir.exists():
            messagebox.showerror("错误", f"找不到 {self.maths_dir} 文件夹")
            return
        
        for md_file in sorted(self.maths_dir.glob('q_*.md')):
            try:
                with open(md_file, 'r', encoding='utf-8') as f:
                    content = f.read()
                
                # 解析ID和标题
                id_match = re.search(r'^id:\s*(\d+)', content, re.MULTILINE)
                title_match = re.search(r'^title:\s*(.+)', content, re.MULTILINE)
                
                question_id = id_match.group(1) if id_match else "?"
                title = title_match.group(1) if title_match else "无标题"
                
                self.questions.append({
                    'file': md_file,
                    'id': question_id,
                    'title': title,
                    'content': content
                })
            except Exception as e:
                print(f"读取文件 {md_file} 时出错: {e}")
        
        self.update_question_list()
    
    def update_question_list(self):
        """更新题目列表显示"""
        self.question_listbox.delete(0, tk.END)
        for q in self.questions:
            self.question_listbox.insert(tk.END, f"题目 {q['id']}: {q['title']}")
    
    def filter_questions(self):
        """搜索过滤"""
        query = self.search_var.get().lower()
        self.question_listbox.delete(0, tk.END)
        
        for q in self.questions:
            if (query in q['id'].lower() or 
                query in q['title'].lower() or 
                query in q['content'].lower()):
                self.question_listbox.insert(tk.END, f"题目 {q['id']}: {q['title']}")
    
    def on_question_select(self, event):
        """选择题目时的处理"""
        selection = self.question_listbox.curselection()
        if not selection:
            return
        
        index = selection[0]
        list_text = self.question_listbox.get(index)
        
        # 从列表文本中提取ID
        id_match = re.search(r'题目 (\d+):', list_text)
        if not id_match:
            return
        
        question_id = id_match.group(1)
        
        # 找到对应的题目
        for q in self.questions:
            if q['id'] == question_id:
                self.load_question(q)
                break
    
    def load_question(self, question):
        """加载题目到编辑器"""
        self.current_file = question['file']
        content = question['content']
        
        # 解析YAML头部
        yaml_match = re.match(r'^---\n(.*?)\n---\n', content, re.DOTALL)
        metadata = {}
        
        if yaml_match:
            yaml_content = yaml_match.group(1)
            for line in yaml_content.split('\n'):
                if ':' in line:
                    key, value = line.split(':', 1)
                    metadata[key.strip()] = value.strip()
            
            rest_content = content[yaml_match.end():]
        else:
            rest_content = content
        
        # 提取各部分内容
        question_text = self.extract_section(rest_content, '题目')
        solution_text = self.extract_section(rest_content, '解答')
        answer_text = self.extract_section(rest_content, '答案')
        
        # 填充表单
        self.title_label.config(text=f"编辑题目 {metadata.get('id', '?')}")
        
        for field_name, entry in self.meta_fields.items():
            if field_name in ['question_text', 'solution_text', 'answer_text']:
                continue
            if field_name == 'id':
                entry.config(state='normal')
            entry.delete(0, tk.END)
            entry.insert(0, metadata.get(field_name, ''))
            if field_name == 'id':
                entry.config(state='readonly')
        
        # 填充文本区域
        self.meta_fields['question_text'].delete('1.0', tk.END)
        self.meta_fields['question_text'].insert('1.0', question_text)
        
        self.meta_fields['solution_text'].delete('1.0', tk.END)
        self.meta_fields['solution_text'].insert('1.0', solution_text)
        
        self.meta_fields['answer_text'].delete('1.0', tk.END)
        self.meta_fields['answer_text'].insert('1.0', answer_text)
        
        # 启用保存按钮
        self.save_btn.config(state=tk.NORMAL)
        
        # 保存原始metadata
        self.current_metadata = metadata
    
    def extract_section(self, content, section_name):
        """提取markdown章节内容"""
        pattern = f'## {section_name}\n(.*?)(?=\n## |$)'
        match = re.search(pattern, content, re.DOTALL)
        return match.group(1).strip() if match else ""
    
    def save_question(self):
        """保存修改"""
        if not self.current_file:
            return
        
        # 构建YAML头部
        yaml_lines = ['---']
        for field_name in ['id', 'title', 'question_type', 'domain', 'difficulty', 'knowledge_point']:
            value = self.meta_fields[field_name].get()
            yaml_lines.append(f'{field_name}: {value}')
        
        # 保留原有的batch和teacher
        if 'batch' in self.current_metadata:
            yaml_lines.append(f"batch: {self.current_metadata['batch']}")
        if 'teacher' in self.current_metadata:
            yaml_lines.append(f"teacher: {self.current_metadata['teacher']}")
        
        yaml_lines.append('---')
        
        # 获取文本内容
        question_text = self.meta_fields['question_text'].get('1.0', tk.END).strip()
        solution_text = self.meta_fields['solution_text'].get('1.0', tk.END).strip()
        answer_text = self.meta_fields['answer_text'].get('1.0', tk.END).strip()
        
        # 构建完整内容
        new_content = '\n'.join(yaml_lines)
        new_content += f'\n\n## 题目\n{question_text}\n\n## 解答\n{solution_text}\n\n## 答案\n{answer_text}\n'
        
        # 保存文件
        try:
            with open(self.current_file, 'w', encoding='utf-8') as f:
                f.write(new_content)
            
            messagebox.showinfo("成功", "保存成功！")
            
            # 重新加载题目列表
            self.load_questions()
        except Exception as e:
            messagebox.showerror("错误", f"保存失败：{str(e)}")

def main():
    root = tk.Tk()
    app = QuestionEditor(root)
    root.mainloop()

if __name__ == '__main__':
    main()

