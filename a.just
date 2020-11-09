struct FileReader {
    file: File,
}

impl FileReader {
    fn open(name: str) -> Self {
        Self {
            file: File { name }
        }
    }

    fn read(self) -> int {
        0
    }
}

struct File { name: str }

let reader = FileReader::open("hello.txt");
reader.read();