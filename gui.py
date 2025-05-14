import customtkinter as ctk
import tkinter as tk
import subprocess
import os
from tkinter import filedialog, messagebox

ctk.set_appearance_mode("dark")
ctk.set_default_color_theme("blue")
C_KEYWORDS = ["int", "void", "char", "float", "double", "struct", "return"]
PROMELA_KEYWORDS = ["proctype", "chan", "if", "fi", "do", "od", "int", "bool"]


class CodeTranslatorApp(ctk.CTk):
    def clear_all(self):
    # Reset all textboxes
        for box in [self.input_box, self.output_box, self.console_box]:
            box.configure(state="normal")
            box.delete("1.0", "end")
            if box != self.input_box:
                box.configure(state="disabled")
        
        self.status_label.configure(text="🧹 Cleared all fields")
    def create_scrollable_textbox(self, parent, label_text, row, column):
        wrapper_frame = ctk.CTkFrame(parent, corner_radius=8, border_width=2, border_color="white")
        wrapper_frame.grid(row=row, column=column, sticky="nsew", padx=10, pady=5)

        wrapper_frame.columnconfigure(0, weight=1)
        wrapper_frame.rowconfigure(1, weight=1)

        # Label
        label_frame = ctk.CTkFrame(wrapper_frame, corner_radius=6)
        label_frame.grid(row=0, column=0, sticky="ew", padx=8, pady=(5, 2))
        label = ctk.CTkLabel(label_frame, text=label_text, font=ctk.CTkFont(size=17, weight="bold"))
        label.pack(side="left", padx=10, pady=2)

        # Properly themed base_frame for textbox + scrollbar
        base_frame = tk.Frame(wrapper_frame, bg="#242424", bd=0, highlightthickness=0)
        base_frame.grid(row=1, column=0, sticky="nsew", padx=0, pady=0)
        base_frame.columnconfigure(0, weight=1)
        base_frame.rowconfigure(0, weight=1)

        # Scrollbar
        scrollbar = tk.Scrollbar(base_frame, bg="#242424", activebackground="#444", troughcolor="#333", bd=0, highlightthickness=0)
        scrollbar.grid(row=0, column=1, sticky="ns")

        # Textbox
        textbox = ctk.CTkTextbox(base_frame, font=("Consolas", 12), wrap="word", yscrollcommand=scrollbar.set)
        textbox.grid(row=0, column=0, sticky="nsew")
        scrollbar.config(command=textbox.yview)

        return textbox




    def __init__(self):
        super().__init__()
        self.title("C to Promela Code Translator")
        self.geometry("1200x800")
        self.minsize(1000, 600)

        # Configure grid layout
        self.columnconfigure(0, weight=1)
        self.columnconfigure(1, weight=1)
        self.rowconfigure(1, weight=3)  # Input
        self.rowconfigure(2, weight=1)  # Output
        self.rowconfigure(3, weight=1)  # Console
        self.rowconfigure(5, weight=0)  # Buttons

        self.create_widgets()

    def create_textbox_frame(self, parent, label_text, row, column, rowspan=1):
        frame = ctk.CTkFrame(parent, corner_radius=8, border_width=2, border_color="white")
        frame.grid(row=row, column=column, rowspan=rowspan, sticky="nsew", padx=10, pady=5)

        frame.columnconfigure(0, weight=1)
        frame.rowconfigure(1, weight=1)

        label_frame = ctk.CTkFrame(frame, corner_radius=6)
        label_frame.grid(row=0, column=0, sticky="ew", padx=8, pady=(5, 2))
        label = ctk.CTkLabel(label_frame, text=label_text, font=ctk.CTkFont(size=17, weight="bold"))
        label.pack(side="left", padx=10, pady=2)

        textbox = ctk.CTkTextbox(frame, font=("Consolas", 12), wrap="word")
        textbox.grid(row=1, column=0, sticky="nsew", padx=5, pady=(0, 5))

        return textbox



    def highlight_keywords(self, textbox, keywords):
        textbox.tag_delete("keyword")
        textbox.tag_config("keyword", foreground="skyblue")

        content = textbox.get("1.0", "end-1c")
        for word in keywords:
            start = "1.0"
            while True:
                start = textbox.search(rf"\\b{word}\\b", start, stopindex="end", regexp=True)
                if not start:
                    break
                end = f"{start}+{len(word)}c"
                textbox.tag_add("keyword", start, end)
                start = end


    def create_widgets(self):
    # Title
    # Title
        title = ctk.CTkLabel(self, text="C to Promela Translator", font=ctk.CTkFont(size=24, weight="bold"))
        title.grid(row=0, column=0, columnspan=2, pady=(10, 5))

        # Grid resizing rules
        self.grid_rowconfigure(1, weight=1)
        self.grid_rowconfigure(2, weight=1)
        self.grid_columnconfigure(0, weight=1)
        self.grid_columnconfigure(1, weight=1)

        # 📝 C Input Code - Left, Full Height (Row 1 + Row 2)
        input_frame = ctk.CTkFrame(self, corner_radius=8, border_width=2, border_color="white")
        input_frame.grid(row=1, column=0, rowspan=2, sticky="nsew", padx=(20, 10), pady=(5, 5))

        input_frame.columnconfigure(0, weight=1)
        input_frame.rowconfigure(1, weight=1)

        input_label = ctk.CTkLabel(input_frame, text="📝 C Input Code", font=ctk.CTkFont(size=17, weight="bold"))
        input_label.grid(row=0, column=0, sticky="w", padx=10, pady=(5, 0))


        self.input_box = self.create_textbox_frame(self, "📝 C Input Code", row=1, column=0, rowspan=2)
        self.input_box.grid(row=1, column=0, sticky="nsew", padx=10, pady=(0, 10))
        self.input_box.insert("1.0", "// Write your C code here")

        # ⚙️ Generated Promela Output - Right Top
        output_frame = ctk.CTkFrame(self, corner_radius=8, border_width=2, border_color="white")
        output_frame.grid(row=1, column=1, sticky="nsew", padx=(10, 20), pady=(5, 2))

        output_frame.columnconfigure(0, weight=1)
        output_frame.rowconfigure(1, weight=1)

        output_label = ctk.CTkLabel(output_frame, text="⚙️ Generated Promela Output", font=ctk.CTkFont(size=17, weight="bold"))
        output_label.grid(row=0, column=0, sticky="w", padx=10, pady=(5, 0))

        self.output_box = self.create_scrollable_textbox(self, "⚙️ Generated Promela Output", row=1, column=1)

        self.output_box.grid(row=1, column=0, sticky="nsew", padx=10, pady=(0, 10))
        self.output_box.insert("1.0", "// Output will appear here")
        self.output_box.configure(state="disabled")



        # 🧾 Console Output - Right Bottom
        console_frame = ctk.CTkFrame(self, corner_radius=8, border_width=2, border_color="white")
        console_frame.grid(row=2, column=1, sticky="nsew", padx=(10, 20), pady=(2, 5))

        console_frame.columnconfigure(0, weight=1)
        console_frame.rowconfigure(1, weight=1)

        console_label = ctk.CTkLabel(console_frame, text="🧾 Console Output", font=ctk.CTkFont(size=17, weight="bold"))
        console_label.grid(row=0, column=0, sticky="w", padx=10, pady=(5, 0))

        self.console_box = self.create_scrollable_textbox(self, "🧾 Console Output", row=2, column=1)
        self.console_box.grid(row=1, column=0, sticky="nsew", padx=10, pady=(0, 10))
        self.console_box.insert("1.0", "// Console logs appear here")
        self.console_box.configure(state="disabled")

        # ── Horizontal Separator ──
        separator = ctk.CTkLabel(self, text="", height=2)
        separator.configure(fg_color="gray")
        separator.grid(row=3, column=0, columnspan=2, sticky="ew", padx=20, pady=(5, 0))

        # ── Bottom Button Frame ──
        button_frame = ctk.CTkFrame(self, fg_color="transparent")
        button_frame.grid(row=4, column=0, columnspan=2, pady=10)

        run_button = ctk.CTkButton(button_frame, text="▶ Convert", command=self.run_converter, width=150)
        run_button.grid(row=0, column=0, padx=10)

        load_button = ctk.CTkButton(button_frame, text="📂 Load input.c", command=self.load_input_file, width=150)
        load_button.grid(row=0, column=1, padx=10)
        self.highlight_keywords(self.input_box, C_KEYWORDS)


        save_output_button = ctk.CTkButton(button_frame, text="💾 Save output.pml", command=self.save_output_file, width=180)
        save_output_button.grid(row=0, column=2, padx=10)

        # ── Status Bar ──
        self.status_label = ctk.CTkLabel(self, text="Ready", anchor="w", font=("Segoe UI", 12))
        self.status_label.grid(row=5, column=0, columnspan=2, sticky="ew", padx=20, pady=(0, 10))
        # Tag configurations for console colors
        self.console_box.tag_config("error", foreground="red")
        self.console_box.tag_config("success", foreground="lightgreen")
        clear_btn = ctk.CTkButton(button_frame, text="🗑️ Clear All", command=self.clear_all, width=150)
        clear_btn.grid(row=0, column=3, padx=10)



    def run_converter(self):
        script_dir = os.path.dirname(os.path.abspath(__file__))
        input_path = os.path.join(script_dir, "input.c")
        maincode_path = os.path.join(script_dir, "maincode.cpp")
        exec_path = os.path.join(script_dir, "converter_exec.exe")
        output_path = os.path.join(script_dir, "output.pml")

        code = self.input_box.get("1.0", "end-1c").strip()
        if not code:
            messagebox.showwarning("Input Required", "Please enter valid C code.")
            return

        try:
            with open(input_path, "w", encoding="utf-8") as f:
                f.write(code)

            compile_proc = subprocess.run(["g++", maincode_path, "-o", exec_path], capture_output=True, text=True)
            run_proc = subprocess.run([exec_path], stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)

            console_output = (
                (compile_proc.stdout or "") +
                (compile_proc.stderr or "") +
                "\n" +
                (run_proc.stdout or "")
                )

            self.console_box.configure(state="normal")
            self.console_box.delete("1.0", "end")

            # Compile output
            if compile_proc.returncode != 0:
                self.console_box.insert("1.0", compile_proc.stderr.strip() + "\n", "error")
            else:
                self.console_box.insert("1.0", compile_proc.stdout.strip() + "\n", "success")

            # Runtime output
            if run_proc.returncode != 0:
                self.console_box.insert("end", run_proc.stderr.strip(), "error")
            else:
                self.console_box.insert("end", run_proc.stdout.strip(), "success")

            self.console_box.configure(state="disabled")


            with open(output_path, "r", encoding="utf-8") as f:
                output = f.read()

            self.output_box.configure(state="normal")
            self.output_box.delete("1.0", "end")
            self.output_box.insert("1.0", output)
            self.highlight_keywords(self.output_box, PROMELA_KEYWORDS)  # ✅ ← ADD THIS LINE
            self.output_box.configure(state="disabled")

            self.status_label.configure(text="✅ Successfully converted input.c to output.pml")

        except subprocess.CalledProcessError as e:
            self.status_label.configure(text="❌ Compilation or execution error")
            messagebox.showerror("Execution Error", str(e))
        except FileNotFoundError as e:
            self.status_label.configure(text="❌ File error: maincode.cpp or output.pml not found")
            messagebox.showerror("Missing File", f"Required file not found:\n{e}")

    def load_input_file(self):
        try:
            with open("input.c", "r", encoding="utf-8") as f:
                code = f.read()
                self.input_box.delete("1.0", "end")
                self.input_box.insert("1.0", code)
                self.status_label.configure(text="📄 Loaded input.c")
        except:
            messagebox.showerror("Error", "Could not load input.c")

    def save_output_file(self):
        output = self.output_box.get("1.0", "end-1c")
        if not output.strip():
            messagebox.showinfo("Nothing to save", "Output is empty.")
            return

        file_path = filedialog.asksaveasfilename(defaultextension=".pml", filetypes=[("Promela Files", "*.pml")])
        if file_path:
            with open(file_path, "w", encoding="utf-8") as f:
                f.write(output)
            self.status_label.configure(text=f"✅ Saved to {file_path}")


if __name__ == "__main__":
    app = CodeTranslatorApp()
    app.mainloop()
