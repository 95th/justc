use justc::{Args, Compiler};
use rustyline::Editor;
use std::{fs, path::PathBuf};

fn main() {
    let args = Args::new();
    if let Some(file_name) = args.file_name {
        run_file(file_name);
    } else {
        run_prompt();
    }
}

fn run_file(file_name: PathBuf) {
    let source = fs::read_to_string(file_name).unwrap();
    let mut c = Compiler::new();
    c.run(source);
}

fn run_prompt() {
    let mut editor = Editor::<()>::new();
    let mut c = Compiler::new();
    loop {
        match editor.readline("$ ") {
            Ok(line) => {
                c.run(line);
            }
            Err(_) => break,
        }
    }
}
