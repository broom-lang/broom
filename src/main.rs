mod pos;
mod lexer;

use clap::Parser;
use rustyline::error::ReadlineError;
use rustyline;

use lexer::Lexer;

#[derive(Parser)]
#[command(author, version, about, long_about = None)] // Read from `Cargo.toml`
struct Args {
    #[arg(long)]
    debug: bool
}

const PROMPT: &'static str = "broom> ";
const HISTORY_FILENAME: &'static str = ".broom-history.txt";
    
fn main() {
    let debug = Args::parse().debug;

    let mut rl = rustyline::Editor::<()>::new().unwrap();

    if rl.load_history(HISTORY_FILENAME).is_err() {
        println!("No previous history.");
    }

    loop {
        match rl.readline(PROMPT) {
            Ok(line) => {
                rl.add_history_entry(line.as_str());

                let mut lexer = Lexer::new(line.as_str(), None);

                for res in lexer {
                    match res {
                        Ok(tok) => println!("{:?}", tok),
                        
                        Err(err) => {
                            eprintln!("{:?}", err);
                            break;
                        }
                    }
                }
            },
            Err(ReadlineError::Interrupted) => {
                println!("CTRL-C");
                break;
            },
            Err(ReadlineError::Eof) => {
                println!("CTRL-D");
                break;
            },
            Err(err) => {
                println!("Error: {:?}", err);
                break;
            }
        }
    }

    rl.save_history(HISTORY_FILENAME).unwrap();
}