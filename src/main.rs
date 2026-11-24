fn main() {
    if let Err(error) = vineflower_rs::frontend::run(std::env::args_os().skip(1)) {
        eprintln!("vineflower-rs: {error}");
        std::process::exit(1);
    }
}
