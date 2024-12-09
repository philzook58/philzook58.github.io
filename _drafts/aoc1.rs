//! ```cargo
//! [dependencies]
//! clap = { version = "4.2", features = ["derive"] }
//! ```

// rustscript or
//cargo -Zscript /tmp/prob1.rs

use std::fs::File;
use std::io::Read;
fn main() -> std::io::Result<()> {
    let mut file = File::open("/tmp/prob1.txt").unwrap();
    //let s = file.read();
    let mut contents = String::new();
    file.read_to_string(&mut contents)?;
    let s = contents.split_whitespace().map(|x| x.parse::<i32>().unwrap()).sum::<i32>();
    println!("{s}");
    println("hithere");
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_main() {
        assert_eq!(main(), Ok(()));
    }
}
