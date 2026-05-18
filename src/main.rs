fn main() {
    match eggbau::cli::run(std::env::args()) {
        Ok(output) => print!("{output}"),
        Err(err) => {
            eprintln!("error: {err}");
            std::process::exit(2);
        }
    }
}
