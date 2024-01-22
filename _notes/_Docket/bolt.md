
Bolt.
<https://github.com/llvm/llvm-project/blob/main/bolt/README.md>
Use perf to get `brstack` or instrucment if not available `perf2bolt-18` converts to bolt.
more complete guide <https://github.com/llvm/llvm-project/blob/main/bolt/docs/OptimizingClang.md>
<https://github.com/llvm/llvm-project/blob/main/bolt/docs/BAT.md> bolt address translation. maintain connection to old profile even after optimizing

Hlavar flake <https://x.com/halvarflake/status/1746623323558023432?s=12&t=pdj9jytXGvxDOXHWwx4_mg> <https://x.com/disruptnhandlr/status/1680975232570642438?s=46&t=pdj9jytXGvxDOXHWwx4_mg>
" llvm-bolt your_binary -o /dev/null -print-cfg -funcs=func1,func2,func_regex.*
-dump-dot-all dumps CFG into a dot file
-print-loops adds nodes color coding (loopy/scalar)
-dot-tooltip-code adds instructions to BB, but .dot needs to be converted with bolt/utils/dot2html/dot2html.py"

<https://research.facebook.com/publications/bolt-a-practical-binary-optimizer-for-data-centers-and-beyond/>

Using LLVM tools.

FDO feedback driven optimziatio
PGO profile guided optimization
link time optimization

sqample based profiling
How much instrumentation. --instrumentation
last Branch Records  <https://lwn.net/Articles/680985/> An introduction to last branch records. `perf record -b workload` . A ring buffer of recent branches

`--emit-relocs` `q`

cfg emission

```bash
echo '
#include <llvm/Object/ELFObjectFile.h>
#include <llvm/Object/ObjectFile.h>
#include <llvm/Support/TargetSelect.h>
#include <llvm/Support/raw_ostream.h>
#include <memory>
#include <iostream>

int main(int argc, char **argv) {
    if (argc < 2) {
        std::cerr << "Usage: " << argv[0] << " <ELF file>\n";
        return 1;
    }

    llvm::InitializeAllTargetInfos();
    llvm::InitializeAllTargetMCs();
    llvm::InitializeAllTargets();
    llvm::InitializeAllTargetInfos();
    llvm::InitializeAllDisassemblers();

    auto ObjOrErr =
        llvm::object::ObjectFile::createObjectFile(argv[1]);
    llvm::outs() << argv[1] << "\n";
    if (!ObjOrErr) {
        std::cerr << "Error loading ELF file.\n";
        return 1;
    }

    auto Obj = (*ObjOrErr).getBinary();
    llvm::outs() << "Loaded ELF file: " << Obj->getFileFormatName() << Obj << "\n";
    // Additional processing can be done here

    return 0;
}

' > /tmp/elf_loader.cpp

clang++ -o /tmp/elf_loader /tmp/elf_loader.cpp `llvm-config-17 --cxxflags --ldflags --system-libs --libs all`

/tmp/elf_loader /bin/ls

```

<https://apt.llvm.org/> get latest toolchain

<https://llvm.org/doxygen/namespacellvm.html> the good docs are in namespace llvm?

```
sudo apt-get llvm-bolt-18
llvm-bolt-18
```

<https://blog.yossarian.net/2021/07/19/LLVM-internals-part-1-bitcode-format>

<https://llvm.org/devmtg/2016-11/Slides/Kleckner-CodeViewInLLVM.pdf> codeview in llvm
