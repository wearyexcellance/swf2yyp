
import os
import json
import queue
import threading
import tkinter as tk
from tkinter import filedialog, messagebox, scrolledtext

import avm2gml


SETTINGS_FILE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "settings.json")


class App:
    def __init__(self, root):
        self.root = root
        root.title("AVM2GML")
        root.geometry("720x560")

        settings = self.load_settings()

        self.swf = tk.StringVar(value=settings.get("swf", "pb2.swf"))
        self.project = tk.StringVar(value=settings.get("project", "cha"))
        self.java = tk.StringVar(value=settings.get("java", avm2gml.DEFAULT_JAVA))
        self.jar = tk.StringVar(value=settings.get("jar", avm2gml.DEFAULT_FFDEC))
        self.merge = tk.StringVar(value=settings.get("merge", ""))

        self.vector = tk.BooleanVar(value=settings.get("vector", True))
        self.transpiler = tk.StringVar(value=settings.get("transpiler", "as3"))

        self.q = queue.Queue()

        self.build_ui()
        self.root.protocol("WM_DELETE_WINDOW", self.close)
        self.poll()

    def load_settings(self):
        try:
            with open(SETTINGS_FILE, "r", encoding="utf-8") as f:
                return json.load(f)
        except (OSError, json.JSONDecodeError):
            return {}

    def save_settings(self):
        settings = {
            "swf": self.swf.get(),
            "project": self.project.get(),
            "java": self.java.get(),
            "jar": self.jar.get(),
            "merge": self.merge.get(),
            "vector": self.vector.get(),
            "transpiler": self.transpiler.get()
        }

        try:
            with open(SETTINGS_FILE, "w", encoding="utf-8") as f:
                json.dump(settings, f, indent=4)
        except OSError as e:
            messagebox.showerror("Settings Error", str(e))

    def close(self):
        self.save_settings()
        self.root.destroy()

    def build_ui(self):
        f = tk.Frame(self.root)
        f.pack(padx=10, pady=10, fill="x")
        f.columnconfigure(1, weight=1)

        rows = [
            ("SWF", self.swf, self.pick_swf),
            ("Project", self.project, None),
            ("Java", self.java, self.pick_java),
            ("FFDec jar", self.jar, self.pick_jar),
            ("Merge (a:b)", self.merge, None)
        ]

        for r, (label, var, pick) in enumerate(rows):
            tk.Label(f, text=label).grid(row=r, column=0, sticky="w")
            tk.Entry(f, textvariable=var).grid(
                row=r, column=1, sticky="ew", padx=4, pady=2
            )

            if pick:
                tk.Button(f, text="...", command=pick).grid(row=r, column=2)

        # Transpiler selection
        transpiler_frame = tk.LabelFrame(
            self.root,
            text="Transpiler Agent"
        )
        transpiler_frame.pack(fill="x", padx=10, pady=5)

        tk.Radiobutton(
            transpiler_frame,
            text="AS2 (AVM1)",
            variable=self.transpiler,
            value="as2"
        ).pack(side="left", padx=15, pady=5)

        tk.Radiobutton(
            transpiler_frame,
            text="AS3 (AVM2)",
            variable=self.transpiler,
            value="as3"
        ).pack(side="left", padx=15, pady=5)

        tk.Checkbutton(
            self.root,
            text="Vector (SVG) sprites, like the template",
            variable=self.vector
        ).pack()

        self.run_btn = tk.Button(
            self.root,
            text="RUN",
            bg="green",
            fg="white",
            command=self.start
        )
        self.run_btn.pack(pady=8)

        self.console = scrolledtext.ScrolledText(self.root, height=15)
        self.console.pack(fill="both", expand=True, padx=10, pady=10)

    def pick_swf(self):
        p = filedialog.askopenfilename(filetypes=[("SWF", "*.swf")])
        if p:
            self.swf.set(p)

    def pick_java(self):
        p = filedialog.askopenfilename(
            filetypes=[("Java", "java*"), ("All files", "*.*")]
        )
        if p:
            self.java.set(p)

    def pick_jar(self):
        p = filedialog.askopenfilename(filetypes=[("JAR", "*.jar")])
        if p:
            self.jar.set(p)

    def poll(self):
        try:
            while True:
                kind, text = self.q.get_nowait()

                if kind == "log":
                    self.console.insert(tk.END, text + "\n")
                    self.console.see(tk.END)

                elif kind == "done":
                    self.run_btn.config(state="normal")
                    messagebox.showinfo("Success", text)

                elif kind == "error":
                    self.run_btn.config(state="normal")
                    messagebox.showerror("Error", text)

        except queue.Empty:
            pass

        self.root.after(100, self.poll)

    def start(self):
        # Save current options immediately, not just when closing.
        self.save_settings()

        # Read Tk variables on the main thread.
        args = {
            "swf": self.swf.get(),
            "project": self.project.get(),
            "java": self.java.get(),
            "jar": self.jar.get(),
            "merge": self.merge.get(),
            "vector": self.vector.get(),
            "transpiler": self.transpiler.get()
        }

        self.run_btn.config(state="disabled")

        threading.Thread(
            target=self.work,
            args=(args,),
            daemon=True
        ).start()

    def work(self, args):
        log = lambda t: self.q.put(("log", t))

        try:
            merge = dict(
                m.split(":", 1)
                for m in args["merge"].split(",")
                if ":" in m
            )

            path = avm2gml.run_pipeline(
                args["swf"],
                args["project"],
                args["java"],
                args["jar"],
                log=log,
                merge=merge or None,
                vector=args["vector"],
                as_version=args["transpiler"]
            )

            self.q.put(("done", f"Finished:\n{path}"))

        except Exception as e:
            log("ERROR: " + str(e))
            self.q.put(("error", str(e)))


if __name__ == "__main__":
    root = tk.Tk()
    App(root)
    root.mainloop()
