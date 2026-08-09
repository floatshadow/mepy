use lalrpop::Configuration;

extern crate lalrpop;

fn main() {
  let mut config = Configuration::new();
  config.generate_in_source_tree();
  config.process_current_dir().unwrap();
}

