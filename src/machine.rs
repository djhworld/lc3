use nix::sys::select::{select, FdSet};
use nix::sys::time::{TimeVal, TimeValLike};
use num_enum::IntoPrimitive;
use num_enum::TryFromPrimitive;
use std::convert::TryFrom;

// Important memory locations
const MR_KBSR: usize = 0xFE00;
const MR_KBDR: usize = 0xFE02;

const TRAP_GETC: u16 = 0x20; /* get character from keyboard, not echoed onto the terminal */
const TRAP_OUT: u16 = 0x21; /* output a character */
const TRAP_PUTS: u16 = 0x22; /* output a word string */
const TRAP_IN: u16 = 0x23; /* get character from keyboard, echoed onto the terminal */
const TRAP_PUTSP: u16 = 0x24; /* output a byte string */
const TRAP_HALT: u16 = 0x25; /* halt the program */

// Registers
const RCOND: usize = 8;

// Flags
const FLAG_NEG: u16 = 2;
const FLAG_ZERO: u16 = 1;
const FLAG_POS: u16 = 0;

#[derive(Debug, Eq, PartialEq, TryFromPrimitive, IntoPrimitive, Copy, Clone)]
#[repr(u16)]
enum OpCode {
    Br = 0, /* branch */
    Add,    /* add  */
    Ld,     /* load */
    St,     /* store */
    Jsr,    /* jump register */
    And,    /* bitwise and */
    Ldr,    /* load register */
    Str,    /* store register */
    Rti,    /* unused */
    Not,    /* bitwise not */
    Ldi,    /* load indirect */
    Sti,    /* store indirect */
    Jmp,    /* jump */
    Res,    /* reserved (unused) */
    Lea,    /* load effective address */
    Trap,   /* execute trap */
}

impl OpCode {
    fn decode(&self, ins: u16) -> Result<Vec<u16>, String> {
        match self {
            OpCode::Add | OpCode::And => {
                let dr = (ins >> 9) & 0x7;
                let sr1 = (ins >> 6) & 0x7;
                let mode = (ins >> 5) & 0x1;
                match mode {
                    1 => {
                        let imm5 = sign_extend(ins & 0x1F, 5);
                        Ok(vec![dr, sr1, mode, imm5])
                    }
                    _ => {
                        let sr2 = ins & 0x7;
                        Ok(vec![dr, sr1, mode, sr2])
                    }
                }
            }
            OpCode::Not => {
                let dr = (ins >> 9) & 0x7;
                let sr1 = (ins >> 6) & 0x7;
                Ok(vec![dr, sr1])
            }
            OpCode::Ld | OpCode::Ldi | OpCode::Lea | OpCode::St | OpCode::Sti => {
                let dr = (ins >> 9) & 0x7;
                let pc_offset = sign_extend(ins & 0x1FF, 9);
                Ok(vec![dr, pc_offset])
            }
            OpCode::Ldr | OpCode::Str => {
                let dr = (ins >> 9) & 0x7;
                let base_register = (ins >> 6) & 0x7;
                let offset = sign_extend(ins & 0x3F, 6);
                Ok(vec![dr, base_register, offset])
            }
            OpCode::Trap => {
                let vector = ins & 0xFF;
                Ok(vec![vector])
            }
            OpCode::Jmp => {
                let base_register = (ins >> 6) & 0x7;
                Ok(vec![base_register])
            }
            OpCode::Jsr => {
                let mode = (ins >> 11) & 0x1;
                if mode == 1 {
                    let offset = sign_extend(ins & 0x7FF, 11);
                    Ok(vec![mode, offset])
                } else {
                    let base_register = (ins >> 6) & 0x7;
                    Ok(vec![mode, base_register])
                }
            }
            OpCode::Br => {
                let n = (ins >> 11) & 0x1;
                let z = (ins >> 10) & 0x1;
                let p = (ins >> 9) & 0x1;
                let offset = sign_extend(ins & 0x1FF, 9);

                Ok(vec![n, z, p, offset])
            }
            OpCode::Res | OpCode::Rti => {
                Err("cannot decode instruction: unsupported op!".to_string())
            }
        }
    }
}

pub struct LC3<'a> {
    pc: u16,
    memory: [u16; 65536],
    regs: [u16; 9],
    halted: bool,
    writer: &'a mut dyn std::io::Write,
    reader: &'a mut dyn OneCharReader,
}

impl<'a> LC3<'a> {
    pub fn new(reader: &'a mut dyn OneCharReader, writer: &'a mut dyn std::io::Write) -> LC3<'a> {
        let mut machine = LC3 {
            memory: [0; 65536],
            regs: [0; 9],
            pc: 0,
            halted: false,
            writer,
            reader,
        };

        machine.setup_trap_handlers();
        machine
    }

    pub fn load(&mut self, origin: usize, program: Vec<u16>) {
        for (i, v) in program.iter().enumerate() {
            self.memory[origin + i] = *v;
        }
    }
    pub fn set_pc(&mut self, pc: u16) {
        self.pc = pc;
    }

    pub fn run(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        while !self.halted {
            self.tick()?;
        }
        Ok(())
    }

    fn tick(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        let ins = self.memory[self.pc as usize];
        let op = OpCode::try_from(ins >> 12)?;
        let decoded = op.decode(ins & 0xFFF)?;
        self.pc = self.pc.wrapping_add(1);

        match op {
            OpCode::Add => {
                let dr = decoded[0] as usize;
                let sr1 = decoded[1] as usize;
                let mode = decoded[2];
                let arg = decoded[3];

                let sr1_val = self.regs[sr1];
                if mode == 1 {
                    self.regs[dr] = sr1_val.wrapping_add(arg);
                } else {
                    self.regs[dr] = sr1_val.wrapping_add(self.regs[arg as usize]);
                }

                self.update_flags(dr);
            }
            OpCode::And => {
                let dr = decoded[0] as usize;
                let sr1 = decoded[1] as usize;
                let mode = decoded[2];
                let arg = decoded[3];

                let sr1_val = self.regs[sr1];
                if mode == 1 {
                    self.regs[dr] = sr1_val & arg;
                } else {
                    self.regs[dr] = sr1_val & self.regs[arg as usize];
                }

                self.update_flags(dr);
            }
            OpCode::Not => {
                let dr = decoded[0] as usize;
                let sr1 = decoded[1] as usize;
                let val = self.regs[sr1];
                self.regs[dr] = !val;
                self.update_flags(dr);
            }
            OpCode::Ld => {
                let dr = decoded[0] as usize;
                let pc_offset = decoded[1];
                self.regs[dr] = self.mem_read(self.pc.wrapping_add(pc_offset))?;
                self.update_flags(dr);
            }
            OpCode::Lea => {
                let dr = decoded[0] as usize;
                let pc_offset = decoded[1];
                self.regs[dr] = self.pc.wrapping_add(pc_offset);
                self.update_flags(dr);
            }
            OpCode::Ldi => {
                let dr = decoded[0] as usize;
                let pc_offset = decoded[1];
                let addr = self.mem_read(self.pc.wrapping_add(pc_offset))?;
                let val = self.mem_read(addr)?;
                self.regs[dr] = val;
                self.update_flags(dr);
            }
            OpCode::Sti => {
                let sr = decoded[0] as usize;
                let pc_offset = decoded[1];
                let value = self.regs[sr];
                let val1 = self.mem_read(self.pc.wrapping_add(pc_offset))?;
                let addr = self.mem_read(val1)?;
                self.memory[addr as usize] = value;
            }
            OpCode::Str => {
                let sr = decoded[0] as usize;
                let br = decoded[1] as usize;
                let offset = decoded[2];

                let br_value = self.regs[br];
                let loc = br_value.wrapping_add(offset);

                self.memory[loc as usize] = self.regs[sr];
            }
            OpCode::Ldr => {
                let dr = decoded[0] as usize;
                let br = decoded[1] as usize;
                let offset = decoded[2];

                let val = self.regs[br];

                let loc = val.wrapping_add(offset);
                self.regs[dr] = self.mem_read(loc)?;
                self.update_flags(dr);
            }
            OpCode::St => {
                let sr = decoded[0] as usize;
                let pc_offset = decoded[1];
                let loc = self.pc.wrapping_add(pc_offset) as usize;
                self.memory[loc] = self.regs[sr];
            }
            OpCode::Trap => {
                let vector = decoded[0];
                self.regs[7] = self.pc;
                self.pc = self.memory[vector as usize];
                self.handle_trap()?;
                self.pc = self.regs[7];
            }
            OpCode::Jmp => {
                let br = decoded[0];
                self.pc = self.regs[br as usize];
            }
            OpCode::Jsr => {
                let mode = decoded[0];
                self.regs[7] = self.pc;
                if mode == 0 {
                    let br = decoded[1];
                    self.pc = self.regs[br as usize];
                } else {
                    let offset = decoded[1];
                    self.pc = self.pc.wrapping_add(offset);
                }
            }
            OpCode::Br => {
                let n = decoded[0];
                let z = decoded[1];
                let p = decoded[2];
                let offset = decoded[3];
                let cond = self.regs[RCOND];

                let current_n: u16 = (cond >> FLAG_NEG) & 0x1;
                let current_z: u16 = (cond >> FLAG_ZERO) & 0x1;
                let current_p: u16 = (cond >> FLAG_POS) & 0x1;

                let set_n = (n & current_n) == 1;
                let set_z = (z & current_z) == 1;
                let set_p = (p & current_p) == 1;

                if set_n || set_z || set_p {
                    self.pc = self.pc.wrapping_add(offset);
                }
            }
            _ => {
                return Err(Box::new(MachineError {
                    contents: "unsupported opcode".to_string(),
                }));
            }
        }

        Ok(())
    }

    fn mem_read(&mut self, addr: u16) -> Result<u16, Box<dyn std::error::Error>> {
        if addr as usize == MR_KBSR {
            if self.check_key() {
                self.memory[MR_KBSR] = 1 << 15;
                self.memory[MR_KBDR] = self.getchar()?;
            } else {
                self.memory[MR_KBSR] = 0;
            }
        }
        Ok(self.memory[addr as usize])
    }

    fn update_flags(&mut self, register: usize) {
        let value = self.regs[register];
        if value == 0 {
            self.regs[RCOND] = 1 << FLAG_ZERO;
        } else if ((value >> 15) & 0x1) == 1 {
            /* a 1 in the left-most bit indicates negative */
            self.regs[RCOND] = 1 << FLAG_NEG;
        } else {
            self.regs[RCOND] = 1 << FLAG_POS;
        }
    }

    fn setup_trap_handlers(&mut self) {
        self.memory[TRAP_GETC as usize] = TRAP_GETC;
        self.memory[TRAP_PUTS as usize] = TRAP_PUTS;
        self.memory[TRAP_PUTSP as usize] = TRAP_PUTSP;
        self.memory[TRAP_HALT as usize] = TRAP_HALT;
        self.memory[TRAP_IN as usize] = TRAP_IN;
        self.memory[TRAP_OUT as usize] = TRAP_OUT;
    }

    fn handle_trap(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        match self.pc {
            TRAP_GETC => self.getc(),
            TRAP_PUTS => self.puts(),
            TRAP_PUTSP => self.putsp(),
            TRAP_HALT => self.halt(),
            TRAP_IN => self.input(),
            TRAP_OUT => self.out(),
            _ => Err(Box::new(MachineError {
                contents: format!("unsupported trap vector: {:x}", self.pc),
            })),
        }
    }

    fn puts(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        let mut start = self.regs[0];
        let mut c: u16 = self.mem_read(start)?;
        while c != 0x0 {
            write!(self.writer, "{}", char::from(c as u8))?;
            start += 1;
            c = self.mem_read(start)?;
        }
        self.writer.flush()?;
        Ok(())
    }

    fn halt(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        self.halted = true;
        Ok(())
    }

    fn putsp(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        let mut start = self.regs[0] as usize;
        let mut c: u16 = self.memory[start];
        loop {
            let char1 = c & 0x00FF;
            write!(self.writer, "{}", char::from(char1 as u8))?;

            let char2 = (c >> 8) & 0x00FF;
            if char2 > 0 {
                write!(self.writer, "{}", char::from(char2 as u8))?;
                start += 1;
                c = self.memory[start];
            } else {
                break;
            }
        }
        self.writer.flush()?;
        Ok(())
    }

    fn out(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        let start = self.regs[0];
        let c: u16 = self.mem_read(start)?;
        if c == 0x00 {
            writeln!(self.writer)?;
        } else {
            write!(self.writer, "{}", char::from(c as u8))?;
        }
        Ok(())
    }

    fn getc(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        self.regs[0] = self.getchar()?;
        Ok(())
    }

    fn getchar(&mut self) -> Result<u16, Box<dyn std::error::Error>> {
        let val = self.reader.get()?;
        let val = val as u16;
        Ok(val)
    }

    fn input(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        write!(self.writer, "> ")?;
        self.writer.flush()?;
        let val = self.reader.get()?;
        let val = val as u16;
        self.regs[0] = val;
        write!(self.writer, "{}", char::from(val as u8))?;
        self.writer.flush()?;
        Ok(())
    }

    fn check_key(&self) -> bool {
        const STDIN_FILENO: i32 = 0;

        let mut readfds = FdSet::new();
        readfds.insert(STDIN_FILENO);

        match select(None, &mut readfds, None, None, &mut TimeVal::zero()) {
            Ok(value) => value == 1,
            Err(_) => false,
        }
    }
}

#[derive(Debug)]
pub struct MachineError {
    contents: String,
}

impl std::fmt::Display for MachineError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", format!("MachineError: {}", self.contents))
    }
}

impl std::error::Error for MachineError {}

pub trait OneCharReader {
    fn get(&mut self) -> Result<u8, Box<dyn std::error::Error>>;
}

pub struct Getcher {
    getc: getch::Getch,
}

impl Getcher {
    pub fn new() -> Self {
        Self {
            getc: getch::Getch::new(),
        }
    }
}

impl Default for Getcher {
    fn default() -> Self {
        Self::new()
    }
}

impl OneCharReader for Getcher {
    fn get(&mut self) -> Result<u8, Box<dyn std::error::Error>> {
        let val = self.getc.getch()?;
        Ok(val)
    }
}

fn sign_extend(n: u16, bit_count: u8) -> u16 {
    if ((n >> (bit_count - 1)) & 1) == 1 {
        n | (0xFFFF << bit_count)
    } else {
        n
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_br_dont() {
        // should not branch at all
        let n = 0;
        let z = 0;
        let p = 0;
        let offset = 23;

        let ins = OpCode::Br.encode(vec![n, z, p, offset]).unwrap();
        let mut writer = DummyWriter::new();
        let mut reader = DummyReader::new();
        let mut lc3 = LC3::new(&mut reader, &mut writer);

        lc3.memory[0] = ins as u16;

        lc3.regs[0] = 0;
        lc3.update_flags(0);
        lc3.regs[0] = 65535;
        lc3.update_flags(0);
        lc3.regs[0] = 1;
        lc3.update_flags(0);
        lc3.tick().unwrap();
        assert_eq!(lc3.pc, 1); //trap vector
    }

    #[test]
    fn test_br_zero() {
        let n = 0;
        let z = 1;
        let p = 0;

        let offset = 23;

        let ins = OpCode::Br.encode(vec![n, z, p, offset]).unwrap();

        let mut writer = DummyWriter::new();
        let mut reader = DummyReader::new();
        let mut lc3 = LC3::new(&mut reader, &mut writer);
        lc3.memory[0] = ins as u16;
        lc3.regs[0] = 0;
        lc3.update_flags(0);
        lc3.tick().unwrap();
        assert_eq!(lc3.pc, 24); //trap vector
    }

    #[test]
    fn test_br_pos() {
        let n = 0;
        let z = 0;
        let p = 1;

        let offset = 23;

        let ins = OpCode::Br.encode(vec![n, z, p, offset]).unwrap();

        let mut writer = DummyWriter::new();
        let mut reader = DummyReader::new();
        let mut lc3 = LC3::new(&mut reader, &mut writer);
        lc3.memory[0] = ins as u16;
        lc3.regs[0] = 100;
        lc3.update_flags(0);
        lc3.tick().unwrap();
        assert_eq!(lc3.pc, 24); //trap vector
    }

    #[test]
    fn test_br_neg() {
        let n = 1;
        let z = 0;
        let p = 0;

        let offset = 23;

        let ins = OpCode::Br.encode(vec![n, z, p, offset]).unwrap();

        let mut writer = DummyWriter::new();
        let mut reader = DummyReader::new();
        let mut lc3 = LC3::new(&mut reader, &mut writer);
        lc3.memory[0] = ins as u16;
        lc3.regs[0] = 65535;
        lc3.update_flags(0);
        lc3.tick().unwrap();
        assert_eq!(lc3.pc, 24); //trap vector
    }

    #[test]
    fn test_trap() {
        let vector = 23;

        let ins = OpCode::Trap.encode(vec![vector]).unwrap();

        let trap: u16 = TRAP_PUTS;
        let mut writer = DummyWriter::new();
        let mut reader = DummyReader::new();
        let mut lc3 = LC3::new(&mut reader, &mut writer);
        lc3.memory[0] = ins as u16;
        lc3.memory[23] = trap;
        lc3.tick().unwrap();
        assert_eq!(lc3.regs[7], 1); // incremented PC
        assert_eq!(lc3.pc, 1); // should restore pc
    }

    #[test]
    fn test_trap_puts() {
        let vector = 23;
        let ins = OpCode::Trap.encode(vec![vector]).unwrap();

        let trap: u16 = TRAP_PUTS;

        let mut writer = DummyWriter::new();
        let mut reader = DummyReader::new();
        let mut lc3 = LC3::new(&mut reader, &mut writer);
        lc3.regs[0] = 3000;
        lc3.memory[0] = ins as u16;
        lc3.memory[23] = trap;

        lc3.memory[3000] = 72;
        lc3.memory[3001] = 69;
        lc3.memory[3002] = 76;
        lc3.memory[3003] = 76;
        lc3.memory[3004] = 79;
        lc3.tick().unwrap();
        assert_eq!(writer.get_string(), String::from("HELLO"));
    }

    #[test]
    fn test_trap_out() {
        let vector = 21;
        let ins = OpCode::Trap.encode(vec![vector]).unwrap();

        let trap: u16 = TRAP_OUT;

        let mut writer = DummyWriter::new();
        let mut reader = DummyReader::new();
        let mut lc3 = LC3::new(&mut reader, &mut writer);
        lc3.regs[0] = 3000;
        lc3.memory[0] = ins as u16;
        lc3.memory[21] = trap;

        lc3.memory[3000] = 72;
        lc3.tick().unwrap();
        assert_eq!(writer.get_string(), String::from("H"));
    }

    #[test]
    fn test_trap_restores_pc() {
        let vector = 21;
        let ins = OpCode::Trap.encode(vec![vector]).unwrap();

        let trap: u16 = TRAP_OUT;

        let mut writer = DummyWriter::new();
        let mut reader = DummyReader::new();
        let mut lc3 = LC3::new(&mut reader, &mut writer);
        lc3.regs[0] = 3000;
        lc3.memory[0] = ins as u16;
        lc3.memory[21] = trap;

        lc3.memory[3000] = 72;
        lc3.tick().unwrap();
        assert_eq!(lc3.pc, 1);
    }

    #[test]
    fn test_jsr() {
        let mode = 0;
        let base_reg = 4;
        let ins = OpCode::Jsr.encode(vec![mode, base_reg]).unwrap();

        let mut writer = DummyWriter::new();
        let mut reader = DummyReader::new();
        let mut lc3 = LC3::new(&mut reader, &mut writer);
        lc3.memory[0] = ins as u16;
        lc3.regs[base_reg as usize] = 9000;
        lc3.tick().unwrap();
        assert_eq!(lc3.regs[7], 1); // incremented PC
        assert_eq!(lc3.pc, 9000);
    }

    #[test]
    fn test_jsr_imm() {
        let mode = 1;
        let offset = 1001;
        let ins = OpCode::Jsr.encode(vec![mode, offset]).unwrap();

        let mut writer = DummyWriter::new();
        let mut reader = DummyReader::new();
        let mut lc3 = LC3::new(&mut reader, &mut writer);
        lc3.memory[0] = ins as u16;
        lc3.tick().unwrap();
        assert_eq!(lc3.regs[7], 1); // incremented PC
        assert_eq!(lc3.pc, 1002);
    }

    #[test]
    fn test_jmp() {
        let br = 3;
        let ins = OpCode::Jmp.encode(vec![br]).unwrap();

        let mut writer = DummyWriter::new();
        let mut reader = DummyReader::new();
        let mut lc3 = LC3::new(&mut reader, &mut writer);

        lc3.regs[br as usize] = 10000;
        lc3.memory[0] = ins as u16;

        lc3.tick().unwrap();
        assert_eq!(lc3.pc, 10000); //trap vector
    }

    #[test]
    fn test_sti() {
        let sr = 0;
        let offset = 10;

        let ins = OpCode::Sti.encode(vec![sr, offset]).unwrap();

        let mut writer = DummyWriter::new();
        let mut reader = DummyReader::new();
        let mut lc3 = LC3::new(&mut reader, &mut writer);
        lc3.regs[sr as usize] = 18;

        lc3.memory[0] = ins as u16;
        lc3.memory[1 + offset as usize] = 23; //pc offset + pc
        lc3.memory[23] = 10000; //pc offset + pc
        lc3.tick().unwrap();
        assert_eq!(lc3.memory[10000], 18);
    }

    #[test]
    fn test_ldi() {
        let dr = 0;
        let offset = 10;

        let ins = OpCode::Ldi.encode(vec![dr, offset]).unwrap();

        let mut writer = DummyWriter::new();
        let mut reader = DummyReader::new();
        let mut lc3 = LC3::new(&mut reader, &mut writer);
        lc3.memory[0] = ins as u16;
        lc3.memory[11] = 10000; //pc offset + pc
        lc3.memory[10000] = 383; // actual value to read
        lc3.tick().unwrap();
        assert_eq!(lc3.regs[dr as usize], 383);
        assert_eq!((lc3.regs[RCOND] >> 0) & 0x1, 1);
    }

    #[test]
    fn test_str() {
        let sr = 3;
        let br = 4;
        let offset = 8;

        let ins = OpCode::Str.encode(vec![sr, br, offset]).unwrap();

        let mut writer = DummyWriter::new();
        let mut reader = DummyReader::new();
        let mut lc3 = LC3::new(&mut reader, &mut writer);
        lc3.regs[sr as usize] = 12;
        lc3.regs[br as usize] = 383;

        lc3.memory[0] = ins as u16;
        lc3.tick().unwrap();
        assert_eq!(lc3.memory[offset as usize + 383], 12);
    }

    #[test]
    fn test_ldr() {
        let dr = 3;
        let br = 4;
        let offset = 8;

        let ins = OpCode::Ldr.encode(vec![dr, br, offset]).unwrap();

        let mut writer = DummyWriter::new();
        let mut reader = DummyReader::new();
        let mut lc3 = LC3::new(&mut reader, &mut writer);
        lc3.regs[br as usize] = 10;
        lc3.memory[0] = ins as u16;
        lc3.memory[10 + (offset as usize)] = 383; // actual value to read
        lc3.tick().unwrap();
        assert_eq!(lc3.regs[dr as usize], 383);
        assert_eq!((lc3.regs[RCOND] >> 0) & 0x1, 1);
    }

    #[test]
    fn test_ldi_flag_zero() {
        let dr = 0;
        let offset = 10;

        let ins = OpCode::Ldi.encode(vec![dr, offset]).unwrap();

        let mut writer = DummyWriter::new();
        let mut reader = DummyReader::new();
        let mut lc3 = LC3::new(&mut reader, &mut writer);
        lc3.memory[0] = ins as u16;
        lc3.memory[11] = 10000; //pc offset + pc
        lc3.memory[10000] = 0; // actual value to read
        lc3.tick().unwrap();
        assert_eq!(lc3.regs[dr as usize], 0);
        assert_eq!((lc3.regs[RCOND] >> 1) & 0x1, 1);
    }

    #[test]
    fn test_ld() {
        let dr = 0;
        let offset = 10;

        let ins = OpCode::Ld.encode(vec![dr, offset]).unwrap();

        let mut writer = DummyWriter::new();
        let mut reader = DummyReader::new();
        let mut lc3 = LC3::new(&mut reader, &mut writer);
        lc3.memory[0] = ins as u16;
        lc3.memory[11] = 10000; //pc offset + pc
        lc3.tick().unwrap();
        assert_eq!(lc3.regs[dr as usize], 10000);
        assert_eq!((lc3.regs[RCOND] >> 0) & 0x1, 1);
    }

    #[test]
    fn test_st() {
        let sr = 0;
        let offset = 10;

        let ins = OpCode::St.encode(vec![sr, offset]).unwrap();
        let mut writer = DummyWriter::new();
        let mut reader = DummyReader::new();
        let mut lc3 = LC3::new(&mut reader, &mut writer);

        lc3.regs[sr as usize] = 18;

        lc3.memory[0] = ins;
        lc3.tick().unwrap();
        assert_eq!(lc3.memory[1 + (offset as usize)], 18);
    }

    #[test]
    fn test_lea() {
        let dr = 0;
        let offset = 10;

        let ins = OpCode::Lea.encode(vec![dr, offset]).unwrap();

        let mut writer = DummyWriter::new();
        let mut reader = DummyReader::new();
        let mut lc3 = LC3::new(&mut reader, &mut writer);
        lc3.memory[0] = ins;
        lc3.tick().unwrap();
        assert_eq!(lc3.regs[dr as usize], 11);
        assert_eq!((lc3.regs[RCOND] >> 0) & 0x1, 1);
    }

    #[test]
    fn test_add() {
        let mode = 0;
        let sr1 = 1;
        for sr2 in 2..8 {
            let dr = 0;
            let ins = OpCode::Add.encode(vec![dr, sr1, mode, sr2]).unwrap();

            let mut writer = DummyWriter::new();
            let mut reader = DummyReader::new();
            let mut lc3 = LC3::new(&mut reader, &mut writer);
            lc3.regs[sr1 as usize] = 5;
            lc3.regs[sr2 as usize] = 6;
            lc3.memory[0] = ins as u16;
            lc3.tick().unwrap();
            assert_eq!(lc3.regs[dr as usize], 11);
        }

        let sr2 = 1;
        for sr1 in 2..8 {
            let dr = 0;
            let ins = OpCode::Add.encode(vec![dr, sr1, mode, sr2]).unwrap();

            let mut writer = DummyWriter::new();
            let mut reader = DummyReader::new();
            let mut lc3 = LC3::new(&mut reader, &mut writer);
            lc3.regs[sr1 as usize] = 5;
            lc3.regs[sr2 as usize] = 6;
            lc3.memory[0] = ins as u16;
            lc3.tick().unwrap();
            assert_eq!(lc3.regs[dr as usize], 11);
        }

        let sr1 = 0;
        let sr2 = 1;
        for dr in 2..8 {
            let ins = OpCode::Add.encode(vec![dr, sr1, mode, sr2]).unwrap();

            let mut writer = DummyWriter::new();
            let mut reader = DummyReader::new();
            let mut lc3 = LC3::new(&mut reader, &mut writer);
            lc3.regs[sr1 as usize] = 5;
            lc3.regs[sr2 as usize] = 6;
            lc3.memory[0] = ins as u16;
            lc3.tick().unwrap();
            assert_eq!(lc3.regs[dr as usize], 11);
        }
    }

    #[test]
    fn test_and() {
        let mode = 0;
        let sr1 = 1;
        for sr2 in 2..8 {
            let dr = 0;
            let ins = OpCode::And.encode(vec![dr, sr1, mode, sr2]).unwrap();

            let mut writer = DummyWriter::new();
            let mut reader = DummyReader::new();
            let mut lc3 = LC3::new(&mut reader, &mut writer);
            lc3.regs[sr1 as usize] = 5;
            lc3.regs[sr2 as usize] = 6;
            lc3.memory[0] = ins as u16;
            lc3.tick().unwrap();
            assert_eq!(lc3.regs[dr as usize], 5 & 6);
        }

        let sr2 = 1;
        for sr1 in 2..8 {
            let dr = 0;
            let ins = OpCode::And.encode(vec![dr, sr1, mode, sr2]).unwrap();

            let mut writer = DummyWriter::new();
            let mut reader = DummyReader::new();
            let mut lc3 = LC3::new(&mut reader, &mut writer);
            lc3.regs[sr1 as usize] = 5;
            lc3.regs[sr2 as usize] = 6;
            lc3.memory[0] = ins as u16;
            lc3.tick().unwrap();
            assert_eq!(lc3.regs[dr as usize], 5 & 6);
        }

        let sr1 = 0;
        let sr2 = 1;
        for dr in 2..8 {
            let ins = OpCode::And.encode(vec![dr, sr1, mode, sr2]).unwrap();

            let mut writer = DummyWriter::new();
            let mut reader = DummyReader::new();
            let mut lc3 = LC3::new(&mut reader, &mut writer);
            lc3.regs[sr1 as usize] = 5;
            lc3.regs[sr2 as usize] = 6;
            lc3.memory[0] = ins as u16;
            lc3.tick().unwrap();
            assert_eq!(lc3.regs[dr as usize], 5 & 6);
        }
    }

    #[test]
    fn test_and_imm() {
        let mode = 1;
        for sr1 in 1..8 {
            let dr = 0;
            let imm = 5;
            let ins = OpCode::And.encode(vec![dr, sr1, mode, imm]).unwrap();

            let mut writer = DummyWriter::new();
            let mut reader = DummyReader::new();
            let mut lc3 = LC3::new(&mut reader, &mut writer);
            lc3.regs[sr1 as usize] = 5;
            lc3.memory[0] = ins as u16;
            lc3.tick().unwrap();
            assert_eq!(lc3.regs[dr as usize], (5 & imm) as u16);
        }

        let sr1 = 0;
        for dr in 1..8 {
            let imm = dr;
            let ins = OpCode::And.encode(vec![dr, sr1, mode, dr]).unwrap();

            let mut writer = DummyWriter::new();
            let mut reader = DummyReader::new();
            let mut lc3 = LC3::new(&mut reader, &mut writer);
            lc3.regs[sr1 as usize] = 5;
            lc3.memory[0] = ins as u16;
            lc3.tick().unwrap();
            assert_eq!(lc3.regs[dr as usize], (5 & imm) as u16);
        }
    }

    #[test]
    fn test_add_imm_neg_flag() {
        let mode = 1;
        let sr1 = 1;
        let dr = 0;
        let imm = 65534;
        let ins = OpCode::Add.encode(vec![dr, sr1, mode, imm]).unwrap();

        let mut writer = DummyWriter::new();
        let mut reader = DummyReader::new();
        let mut lc3 = LC3::new(&mut reader, &mut writer);
        let val = 65535;
        lc3.regs[sr1 as usize] = val;
        lc3.memory[0] = ins as u16;
        lc3.tick().unwrap();
        assert_eq!(lc3.regs[dr as usize], 65533);
        assert_eq!((lc3.regs[RCOND] >> 2) & 0x1, 1);
    }

    #[test]
    fn test_add_imm_neg_flag2() {
        let mode = 1;
        let sr1 = 1;
        let dr = 0;

        let mut writer = DummyWriter::new();
        let mut reader = DummyReader::new();

        for imm in 65520..65535 {
            let ins = OpCode::Add.encode(vec![dr, sr1, mode, imm]).unwrap();
            let mut lc3 = LC3::new(&mut reader, &mut writer);
            let val = 65535;
            lc3.regs[sr1 as usize] = val;
            lc3.memory[0] = ins as u16;
            lc3.tick().unwrap();
            assert_eq!(
                lc3.regs[dr as usize],
                val.wrapping_add(sign_extend(imm & 0x1F, 5))
            );
            assert_eq!((lc3.regs[RCOND] >> 2) & 0x1, 1);
        }
    }

    #[test]
    fn test_add_imm() {
        let mode = 1;
        for sr1 in 1..8 {
            let dr = 0;
            let imm = 5;
            let ins = OpCode::Add.encode(vec![dr, sr1, mode, imm]).unwrap();

            let mut writer = DummyWriter::new();
            let mut reader = DummyReader::new();
            let mut lc3 = LC3::new(&mut reader, &mut writer);
            lc3.regs[sr1 as usize] = sr1 + 3;
            lc3.memory[0] = ins as u16;
            lc3.tick().unwrap();
            assert_eq!(lc3.regs[dr as usize], (sr1 + 3 + imm) as u16);
        }

        let sr1 = 0;
        for dr in 1..8 {
            let mut writer = DummyWriter::new();
            let mut reader = DummyReader::new();
            let mut lc3 = LC3::new(&mut reader, &mut writer);
            let imm = dr;
            let ins = OpCode::Add.encode(vec![dr, sr1, mode, dr]).unwrap();

            lc3.regs[sr1 as usize] = sr1 + 3;
            lc3.memory[0] = ins;
            lc3.tick().unwrap();
            assert_eq!(lc3.regs[dr as usize], (sr1 + 3 + imm) as u16);
        }
    }

    #[test]
    fn test_not() {
        for sr1 in 1..8 {
            let dr = 0;
            let ins = OpCode::Not.encode(vec![dr, sr1]).unwrap();

            let mut writer = DummyWriter::new();
            let mut reader = DummyReader::new();
            let mut lc3 = LC3::new(&mut reader, &mut writer);
            lc3.regs[sr1 as usize] = sr1 + 1;
            lc3.memory[0] = ins as u16;
            lc3.tick().unwrap();
            assert_eq!(lc3.regs[dr as usize], !(sr1 + 1));
        }
    }
    impl OpCode {
        fn encode(&self, vals: Vec<u16>) -> Result<u16, String> {
            let op: u16 = (*self).into();
            match self {
                OpCode::Add | OpCode::And => {
                    let mut ins: u16 = op << 12;
                    ins |= vals[0] << 9;
                    ins |= vals[1] << 6;

                    let mode = vals[2];
                    if mode == 1 {
                        ins |= 1 << 5;
                        ins |= vals[3] & 0x1F;
                        Ok(ins)
                    } else {
                        ins |= 0 << 5;
                        ins |= vals[3] & 0x7;
                        Ok(ins)
                    }
                }
                OpCode::Not => {
                    let mut ins: u16 = op << 12;
                    ins |= vals[0] << 9;
                    ins |= vals[1] << 6;
                    ins |= 0x3F;
                    Ok(ins)
                }
                OpCode::Ld | OpCode::Ldi | OpCode::Lea | OpCode::St | OpCode::Sti => {
                    let mut ins = op << 12;
                    ins |= vals[0] << 9;
                    ins |= vals[1] & 0x1FF;
                    Ok(ins)
                }
                OpCode::Ldr | OpCode::Str => {
                    let mut ins: u16 = op << 12;
                    ins |= vals[0] << 9; //dr
                    ins |= vals[1] << 6; //br
                    ins |= vals[2] & 0x3F; //offset
                    Ok(ins)
                }
                OpCode::Trap => {
                    let mut ins: u16 = op << 12;
                    ins |= vals[0] & 0xFF; //vector
                    Ok(ins)
                }
                OpCode::Jmp => {
                    let mut ins: u16 = op << 12;
                    ins |= 0 << 9; //dr
                    ins |= vals[0] << 6; //br
                    Ok(ins)
                }
                OpCode::Jsr => {
                    let mut ins: u16 = op << 12;
                    let mode = vals[0];
                    if mode == 1 {
                        ins |= 1 << 11;
                        ins |= vals[1] & 0x7FF;
                    } else {
                        ins |= 0 << 11;
                        ins |= (vals[1] & 0x7) << 6;
                    }
                    Ok(ins)
                }
                OpCode::Br => {
                    let mut ins: u16 = op << 12;
                    let current_n = vals[0] & 0x1;
                    let current_z = vals[1] & 0x1;
                    let current_p = vals[2] & 0x1;
                    ins |= current_n << 11;
                    ins |= current_z << 10;
                    ins |= current_p << 9;
                    ins |= vals[3] & 0x1FF;
                    Ok(ins)
                }
                OpCode::Res | OpCode::Rti => {
                    Err("cannot decode instruction: unsupported op!".to_string())
                }
            }
        }
    }

    struct DummyReader {
        value: Option<u8>,
    }

    impl DummyReader {
        fn new() -> Self {
            Self { value: None }
        }

        fn set(&mut self, val: u8) {
            self.value = Some(val);
        }

        fn clear(&mut self) {
            self.value = None;
        }
    }

    impl OneCharReader for DummyReader {
        fn get(&mut self) -> Result<u8, Box<dyn std::error::Error>> {
            let value = self.value.unwrap();
            self.clear();
            Ok(value)
        }
    }

    struct DummyWriter {
        values: Vec<u8>,
    }

    impl DummyWriter {
        fn new() -> Self {
            Self { values: Vec::new() }
        }

        fn get_string(&self) -> String {
            String::from_utf8(self.values.clone()).unwrap()
        }
    }

    impl std::io::Write for DummyWriter {
        fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
            let mut pushed = 0;
            for v in buf {
                self.values.push(*v);
                pushed += 1;
            }
            Ok(pushed)
        }

        fn flush(&mut self) -> std::io::Result<()> {
            Ok(())
        }
    }
}
