use std::path::PathBuf;
use structopt::StructOpt;

#[derive(StructOpt)]
pub struct Args {
    #[structopt(name = "FILE_NAME")]
    pub file_name: Option<PathBuf>,
}

impl Default for Args {
    fn default() -> Self {
        Self::new()
    }
}

impl Args {
    pub fn new() -> Self {
        Self::from_args()
    }
}
