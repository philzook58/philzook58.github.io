
Print out offsets via C introspection

```bash
echo "
#include <elf.h>
int main(){
    printf("ep_type: %d\n", ET_EXEC);
    printf("ep_type: %d\n", ET_DYN);



}
"
```

## Dwarf write

<https://github.com/gimli-rs/gimli/blob/master/crates/examples/src/bin/simple.rs>

```rust
//cargo-deps: gimli, object, memmap2
//! A simple example of parsing `.debug_info`.

use object::{Object, ObjectSection};
use std::{borrow, env, fs};

fn main() {
    for path in env::args().skip(1) {
        let file = fs::File::open(&path).unwrap();
        let mmap = unsafe { memmap2::Mmap::map(&file).unwrap() };
        let object = object::File::parse(&*mmap).unwrap();
        let endian = if object.is_little_endian() {
            gimli::RunTimeEndian::Little
        } else {
            gimli::RunTimeEndian::Big
        };
        dump_file(&object, endian).unwrap();
    }
}

fn dump_file(object: &object::File, endian: gimli::RunTimeEndian) -> Result<(), gimli::Error> {
    // Load a section and return as `Cow<[u8]>`.
    let load_section = |id: gimli::SectionId| -> Result<borrow::Cow<[u8]>, gimli::Error> {
        match object.section_by_name(id.name()) {
            Some(ref section) => Ok(section
                .uncompressed_data()
                .unwrap_or(borrow::Cow::Borrowed(&[][..]))),
            None => Ok(borrow::Cow::Borrowed(&[][..])),
        }
    };

    // Load all of the sections.
    let dwarf_cow = gimli::Dwarf::load(&load_section)?;

    // Borrow a `Cow<[u8]>` to create an `EndianSlice`.
    let borrow_section: &dyn for<'a> Fn(
        &'a borrow::Cow<[u8]>,
    ) -> gimli::EndianSlice<'a, gimli::RunTimeEndian> =
        &|section| gimli::EndianSlice::new(section, endian);

    // Create `EndianSlice`s for all of the sections.
    let dwarf = dwarf_cow.borrow(&borrow_section);

    // Iterate over the compilation units.
    let mut iter = dwarf.units();
    while let Some(header) = iter.next()? {
        println!(
            "Unit at <.debug_info+0x{:x}>",
            header.offset().as_debug_info_offset().unwrap().0
        );
        let unit = dwarf.unit(header)?;

        // Iterate over the Debugging Information Entries (DIEs) in the unit.
        let mut depth = 0;
        let mut entries = unit.entries();
        while let Some((delta_depth, entry)) = entries.next_dfs()? {
            depth += delta_depth;
            println!("<{}><{:x}> {}", depth, entry.offset().0, entry.tag());

            // Iterate over the attributes in the DIE.
            let mut attrs = entry.attrs();
            while let Some(attr) = attrs.next()? {
                println!("   {}: {:?}", attr.name(), attr.value());
            }
        }
    }
    Ok(())
}

```

```C
typedef struct DIE{

}

typedef 

__attribute__(section(".dwarf_info")) DIE dwarf_info[] = 
{
DIE{
    .DIE_TAG: DW_TAG_compile_unit,
    DIE_CHILDREN: 1,
    DIE_ATTRS: {
        DW_AT_name: "main.c",
        DW_AT_language: DW_LANG_C,
        DW_AT_low_pc: 0x400000,
        DW_AT_high_pc: 0x400100,
        DW_AT_stmt_list: 0x400200,
    }
}
};

```

Idea: pretty printing a global C data structure into the .data section is kind of the eaisest way to turn a textual representation into a binary format

```bash
sudo apt install libdwarf-dev
```

Could also possibly use LLVm dwarf headers?

```bash
echo "
#include <dwarf.h>



" > /tmp/dwarf.c
gcc -I /usr/include/libdwarf/ -c /tmp/dwarf.c -o /tmp/dwarf.o


```

```
#include <dwarf.h>

int main(){
    // open file, go to dwarf entry point.

}
