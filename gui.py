import customtkinter as ctk
import subprocess
from tkinter import filedialog, messagebox

ctk.set_appearance_mode("dark")
ctk.set_default_color_theme("blue")

class CodeTranslatorApp(ctk.CTk):
    def __init__(self):
        super().__init__()
        self.title("🌐 C to Promela Code Translator")
        self.geometry("1200x700")
        self.minsize(1000, 600)

        # Layout
        self.columnconfigure(0, weight=1)
        self.columnconfigure(1, weight=1)
        self.rowconfigure(1, weight=1)

        self.create_widgets()

    def create_widgets(self):
        # Title
        title = ctk.CTkLabel(self, text="C to Promela Translator", font=ctk.CTkFont(size=22, weight="bold"))
        title.grid(row=0, column=0, columnspan=2, pady=(10, 5))

        # Text Areas
        self.input_box = ctk.CTkTextbox(self, font=("Consolas", 14), wrap="word", corner_radius=8)
        self.input_box.grid(row=1, column=0, sticky="nsew", padx=(20, 10), pady=10)
        self.input_box.insert("1.0", "// Write your C code here")

        self.output_box = ctk.CTkTextbox(self, font=("Consolas", 14), wrap="word", corner_radius=8)
        self.output_box.grid(row=1, column=1, sticky="nsew", padx=(10, 20), pady=10)
        self.output_box.insert("1.0", "// Output will appear here")
        self.output_box.configure(state="disabled")

        # Buttons
        button_frame = ctk.CTkFrame(self, fg_color="transparent")
        button_frame.grid(row=2, column=0, columnspan=2, pady=10)

        run_button = ctk.CTkButton(button_frame, text="▶ Convert", command=self.run_converter, width=150)
        run_button.grid(row=0, column=0, padx=10)

        load_button = ctk.CTkButton(button_frame, text="📂 Load input.c", command=self.load_input_file, width=150)
        load_button.grid(row=0, column=1, padx=10)

        save_output_button = ctk.CTkButton(button_frame, text="💾 Save output.spin", command=self.save_output_file, width=180)
        save_output_button.grid(row=0, column=2, padx=10)

        # Status bar
        self.status_label = ctk.CTkLabel(self, text="Ready", anchor="w", font=("Segoe UI", 12))
        self.status_label.grid(row=3, column=0, columnspan=2, sticky="ew", padx=20, pady=(0, 10))

    def run_converter(self):
        code = self.input_box.get("1.0", "end-1c").strip()
        if not code:
            messagebox.showwarning("Input Required", "Please enter valid C code.")
            return

        try:
            with open("input.c", "w") as f:
                f.write(code)

            subprocess.run(["g++", "maincode.cpp", "-o", "converter_exec"], check=True)
            subprocess.run(["./converter_exec"], check=True)

            with open("output.spin", "r") as f:
                output = f.read()

            self.output_box.configure(state="normal")
            self.output_box.delete("1.0", "end")
            self.output_box.insert("1.0", output)
            self.output_box.configure(state="disabled")

            self.status_label.configure(text="✅ Successfully converted input.c to output.spin")

        except subprocess.CalledProcessError as e:
            self.status_label.configure(text="❌ Compilation or execution error")
            messagebox.showerror("Execution Error", str(e))
        except FileNotFoundError:
            self.status_label.configure(text="❌ File error: maincode.cpp or input.c not found")
            messagebox.showerror("Missing File", "Required file not found.")

    def load_input_file(self):
        try:
            with open("input.c", "r") as f:
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

        file_path = filedialog.asksaveasfilename(defaultextension=".spin", filetypes=[("Promela Files", "*.spin")])
        if file_path:
            with open(file_path, "w") as f:
                f.write(output)
            self.status_label.configure(text=f"✅ Saved to {file_path}")

if __name__ == "__main__":
    app = CodeTranslatorApp()
    app.mainloop()
