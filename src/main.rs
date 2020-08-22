pub mod machine;
#[macro_use]
extern crate simple_error;

use file_utils::read::Read;
use machine::*;
use std::env;
use std::error::Error;

fn main() -> Result<(), Box<dyn Error>> {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        bail!("Please provide a binary file as the first argument, e.g. ./2048.obj")
    }

    let stdout = std::io::stdout();
    let mut stdout_lock = stdout.lock();
    let mut reader = Getcher::new();
    let mut lc3_computer = LC3::new(&mut reader, &mut stdout_lock);

    let rom_file = args.get(1).unwrap();
    let (origin, rom) = load_rom(rom_file)?;

    lc3_computer.load(origin, rom);
    lc3_computer.set_pc(origin as u16);
    lc3_computer.run()
}

fn load_rom(file: &str) -> Result<(usize, Vec<u16>), Box<dyn std::error::Error>> {
    let mut file = std::fs::File::open(file)?;

    let origin = swap_endian(file.read_u16()?) as usize;
    let mut rom: Vec<u16> = Vec::new();

    loop {
        let result = file.read_u16();

        if let Err(err) = result {
            match err.kind() {
                std::io::ErrorKind::UnexpectedEof => break,
                _ => return Err(Box::new(err)),
            };
        }

        let result = swap_endian(result.unwrap());
        rom.push(result);
    }

    Ok((origin, rom))
}

fn swap_endian(x: u16) -> u16 {
    (x << 8) | (x >> 8)
}
