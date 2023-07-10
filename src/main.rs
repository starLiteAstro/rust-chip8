use interpreter::ChipState;

mod interpreter;

fn main() {
    env_logger::init();

    let mut chip8_vm = ChipState::new(700);
    chip8_vm.load("roms/Space Invaders.ch8").unwrap();
    chip8_base::run(chip8_vm);
}
