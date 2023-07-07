mod font;

use chip8_base::{Display, Interpreter, Keys, Pixel};
use rand::Rng;
use std::time::Duration;

pub struct ChipState {
    memory: [u8; 4096],
    program_counter: u16,
    stack_pointer: u8,
    stack: [u16; 16],
    registers: [u8; 16],
    index_register: u16,
    delay_timer: u8,
    sound_timer: u8,
    ticker: u32,
    max_ticks: u32,
    display: chip8_base::Display,
    clock_speed: Duration,
}

impl Interpreter for ChipState {
    fn step(&mut self, keys: &Keys) -> Option<Display> {
        let instruction = self.fetch();
        let update = self.execute(instruction, keys);

        // Update ticks
        self.ticker += 1;
        if self.ticker == self.max_ticks {
            self.ticker = 0;
            self.delay_timer = self.delay_timer.saturating_sub(1);
            self.sound_timer = self.sound_timer.saturating_sub(1);
        }
        update
    }

    fn speed(&self) -> Duration {
        self.clock_speed
    }

    fn buzzer_active(&self) -> bool {
        self.sound_timer != 0
    }
}

impl ChipState {
    pub fn new(clock_freq: u32) -> Self {
        let mut memory = [0_u8; 4096];
        memory[0x50..(0x50 + 80)].copy_from_slice(&font::FONT); // 0x50 is the start of the fontset

        ChipState {
            memory: [0; 4096],
            program_counter: 0,
            stack_pointer: 0,
            stack: [0; 16],
            registers: [0; 16],
            index_register: 0,
            delay_timer: 0,
            sound_timer: 0,
            ticker: 0,
            max_ticks: (clock_freq as f64 / 60 as f64).round() as u32,
            display: [[Pixel::default(); 64]; 32],
            clock_speed: Duration::from_secs_f64(1_f64 / clock_freq as f64),
        }
    }

    pub fn load(&mut self, filename: &str) -> std::io::Result<&mut Self> {
        let program = std::fs::read(filename)?;
        self.memory[0x200..0x200 + program.len()].copy_from_slice(&program);
        self.program_counter = 0x200;
        Ok(self)
    }

    fn fetch(&mut self) -> u16 {
        let instruction = u16::from_be_bytes([
            self.memory[self.program_counter as usize],
            self.memory[(self.program_counter + 1) as usize],
        ]);
        self.program_counter += 2;
        self.program_counter & 0x0FFF;
        instruction
    }

    // Break u16 instruction into 4 u8 nibbles
    fn nibbles(n: u16) -> (u8, u8, u8, u8) {
        let n3 = (n >> 12) as u8;
        let n2 = ((n >> 8) & 0b1111) as u8;
        let n1 = ((n >> 4) & 0b1111) as u8;
        let n0 = (n & 0b1111) as u8;
        (n3, n2, n1, n0)
    }

    fn execute(&mut self, instruction: u16, keys: &Keys) -> Option<Display> {
        match Self::nibbles(instruction) {
            // 0000 NOP: nothing
            (0x0, 0x0, 0x0, 0x0) => (),
            // 00E0 CLS: clear display
            (0x0, 0x0, 0xE, 0x0) => {
                self.display = [[Pixel::default(); 64]; 32];
                return Some(self.display);
            }
            // 00EE RET: return from subroutine
            (0x0, 0x0, 0xE, 0xE) => {
                self.program_counter = self.stack[self.stack_pointer as usize];
                self.stack_pointer -= 1;
            }
            // 1nnn JP addr: jump to location nnn
            (0x1, n2, n1, n0) => {
                self.program_counter = ((n2 as u16) << 8) | ((n1 as u16) << 4) | n0 as u16;
            }
            // 2nnn CALL addr: call subroutine at nnn
            (0x2, n2, n1, n0) => {
                self.stack_pointer += 1;
                self.stack[self.stack_pointer as usize] = self.program_counter;
                self.program_counter = ((n2 as u16) << 8) | ((n1 as u16) << 4) | n0 as u16;
            }
            // 3xkk SE Vx, byte: skip next instruction if Vx = kk
            (0x3, x, n1, n0) => {
                if self.registers[x as usize] == ((n1 << 4) | n0) {
                    self.program_counter += 2;
                }
            }
            // 4xkk SNE Vx, byte: skip next instruction if Vx != kk
            (0x4, x, n1, n0) => {
                if self.registers[x as usize] != ((n1 << 4) | n0) {
                    self.program_counter += 2;
                }
            }
            // 5xy0 SE Vx, Vy: skip next instruction if Vx = Vy
            (0x5, x, y, 0x0) => {
                if self.registers[x as usize] == self.registers[y as usize] {
                    self.program_counter += 2;
                }
            }
            // 6xkk LD Vx, byte: set Vx = kk
            (0x6, x, n1, n0) => {
                self.registers[x as usize] = (n1 << 4) | n0;
            }
            // 7xkk ADD Vx, byte: set Vx = Vx + kk
            (0x7, x, n1, n0) => {
                self.registers[x as usize] =
                    self.registers[x as usize].wrapping_add((n1 << 4) | n0);
            }
            // 8xy0 LD Vx, Vy: set Vx = Vy
            (0x8, x, y, 0x0) => {
                self.registers[x as usize] = self.registers[y as usize];
            }
            // 8xy1 OR Vx, Vy: set Vx = Vx OR Vy
            (0x8, x, y, 0x1) => {
                self.registers[x as usize] |= self.registers[y as usize];
            }
            // 8xy2 AND Vx, Vy: set Vx = Vx AND Vy
            (0x8, x, y, 0x2) => {
                self.registers[x as usize] &= self.registers[y as usize];
            }
            // 8xy3 XOR Vx, Vy: set Vx = Vx XOR Vy
            (0x8, x, y, 0x3) => {
                self.registers[x as usize] ^= self.registers[y as usize];
            }
            // 8xy4 ADD Vx, Vy: set Vx = Vx + Vy, set VF = carry
            (0x8, x, y, 0x4) => {
                let (sum, overflow) =
                    self.registers[x as usize].overflowing_add(self.registers[y as usize]);
                self.registers[x as usize] = sum;
                self.registers[0xF] = overflow as u8;
            }
            // 8xy5 SUB Vx, Vy: set Vx = Vx - Vy, set VF = NOT borrow
            (0x8, x, y, 0x5) => {
                let (diff, overflow) =
                    self.registers[x as usize].overflowing_sub(self.registers[y as usize]);
                self.registers[x as usize] = diff;
                self.registers[0xF] = !overflow as u8;
            }
            // 8xy6 SHR Vx {, Vy}: set Vx = Vx SHR 1
            (0x8, x, y, 0x6) => {
                self.registers[0xF] = self.registers[x as usize] & 0x1;
                self.registers[x as usize] >>= 1;
            }
            // 8xy7 SUBN Vx, Vy: set Vx = Vy - Vx, set VF = NOT borrow
            (0x8, x, y, 0x7) => {
                let (diff, overflow) =
                    self.registers[y as usize].overflowing_sub(self.registers[x as usize]);
                self.registers[x as usize] = diff;
                self.registers[0xF] = !overflow as u8;
            }
            // 8xyE SHL Vx {, Vy}: set Vx = Vx SHL 1
            (0x8, x, y, 0xE) => {
                self.registers[0xF] = self.registers[x as usize] & 0x1;
                self.registers[x as usize] <<= 1;
            }
            // 9xy0 SNE Vx, Vy: skip next instruction if Vx != Vy
            (0x9, x, y, 0x0) => {
                if self.registers[x as usize] != self.registers[y as usize] {
                    self.program_counter += 2;
                }
            }
            // Annn LD I, addr: set I = nnn
            (0xA, n2, n1, n0) => {
                self.index_register = ((n2 as u16) << 8) | ((n1 as u16) << 4) | n0 as u16;
            }
            // Bnnn JP V0, addr
            (0xB, n2, n1, n0) => {
                self.program_counter = ((((n2 as u16) << 8) | ((n1 as u16) << 4) | n0 as u16)
                    + self.registers[0] as u16)
                    & 0xFFF;
            }
            // Cxkk RND Vx, byte: set Vx = randon byte AND kk
            (0xC, x, n1, n0) => {
                let rand = rand::thread_rng().gen_range(0..=255);
                self.registers[x as usize] = rand & ((n1 << 4) | n0);
            }
            // Dxyn DRW Vx, Vy, nibble: display n-byte sprite starting at memory location I at (Vx, Vy), set VF = collision
            (0xD, x, y, n) => {
                let x = self.registers[x as usize] % 64;
                let y = self.registers[y as usize] % 32;
                self.registers[0xF] = 0;
                let index = self.index_register as usize;
                let sprite = &self.memory[index..index + n as usize];

                for (i, row) in sprite.iter().enumerate() {
                    let pix_y = y + i as u8;
                    if pix_y >= 32 {
                        break;
                    }
                    for j in 0..8 {
                        let pix_x = x + j;
                        if pix_x >= 64 {
                            break;
                        }
                        let old_pix = &mut self.display[pix_y as usize][pix_x as usize];
                        let mask = 2_u8.pow(7 - j as u32);
                        let new_u8 = (row & mask) >> (7 - j);
                        let new_pix: Pixel = new_u8.try_into().unwrap();
                        if (new_pix & *old_pix).into() {
                            // if collision
                            self.registers[0xF] = 1
                        }
                        *old_pix ^= new_pix;
                    }
                }
                return Some(self.display);
            }
            // Ex9E SKP Vx: skip next instruction if key with the value of Vx is pressed
            (0xE, x, 0x9, 0xE) => {
                if keys[self.registers[x as usize] as usize] {
                    self.program_counter += 2;
                }
            }
            // ExA1 SKNP Vx: skip next instruction if key with the value of Vx is not pressed
            (0xE, x, 0xA, 0x1) => {
                if !keys[self.registers[x as usize] as usize] {
                    self.program_counter += 2;
                }
            }
            // Fx07 LD Vx, DT: set Vx = delay timer value
            (0xF, x, 0x0, 0x7) => {
                self.registers[x as usize] = self.delay_timer;
            }
            // Fx0A LD Vx, K: wait for a key press, store the value of the key in Vx
            (0xF, x, 0x0, 0xA) => {
                for (i, key) in keys.iter().enumerate() {
                    if *key {
                        self.registers[x as usize] = i as u8;
                        return None;
                    }
                }
                self.program_counter -= 2;
            }
            // Fx15 LD DT, Vx: set delay timer = Vx
            (0xF, x, 0x1, 0x5) => {
                self.delay_timer = self.registers[x as usize];
            }
            // Fx18 LD ST, Vx: set sound timer = Vx
            (0xF, x, 0x1, 0x8) => {
                self.sound_timer = self.registers[x as usize];
            }
            // Fx1E ADD I, Vx: set I = I + Vx
            (0xF, x, 0x1, 0xE) => {
                self.index_register =
                    (self.index_register + self.registers[x as usize] as u16) & 0xFFF;
            }
            // Fx29 LD F, Vx: set I = location of sprite for digit Vx
            (0xF, x, 0x2, 0x9) => {
                self.index_register = 0x50 + (self.registers[x as usize] as u16) * 5;
                // Font starts at 0x50
            }
            // Fx33 LD B, Vx: store BCD representation of Vx in memory locations I, I+1, and I+2
            (0xF, x, 0x3, 0x3) => {
                let index = self.index_register as usize;
                let val = self.registers[x as usize];
                self.memory[index] = val / 100;
                self.memory[index + 1] = (val / 10) % 10;
                self.memory[index + 2] = val % 10;
            }
            // Fx55 LD [I], Vx: store registers V0 through Vx in memory starting at location I
            (0xF, x, 0x5, 0x5) => {
                let index = self.index_register as usize;
                for reg_i in 0..=x as usize {
                    self.memory[index + reg_i] = self.registers[reg_i];
                }
            }
            // Fx65 LD Vx, [I]: read registers V0 through Vx from memory starting at location I
            (0xF, x, 0x6, 0x5) => {
                let index = self.index_register as usize;
                for reg_i in 0..=x as usize {
                    self.registers[reg_i] = self.memory[index + reg_i];
                }
            }
            _ => panic!("Unknown opcode: {:x}", instruction),
        };
        None
    }
}
