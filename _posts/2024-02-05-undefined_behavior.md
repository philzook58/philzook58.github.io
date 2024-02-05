---
date: 2024-02-05
layout: post
title: Tools for Detecting Undefined Behavior in My Bad C Example
---

Try in colab:
<https://colab.research.google.com/github/philzook58/philzook58.github.io/blob/master/pynb/2024-02-05-undefined_behavior.ipynb>

I posted a [little tutorial](https://www.philipzucker.com/cbmc_tut/) on [CBMC](https://github.com/diffblue/cbmc), the C Bounded model checker last week.

It made it to the front page of [Hacker news](https://news.ycombinator.com/item?id=39191507), which is neat. What I didn't expect is how people latched onto the uninitialized read in this example

```python
%%file /tmp/ex1.c
#include <assert.h>
int main(){
    int x;
    if (x <= 42){
            assert(x != 12345);
    }
}

```

    Writing /tmp/ex1.c

This is a serious issue that CBMC does not check for. It is a tool that can fairly easily and effectively answer certain kinds of questions, but not all. It is in the [process of getting better](https://github.com/diffblue/cbmc/issues/7732)

CBMC on it's own is insufficient to guarantee that a program does what you want and what you expect or that it obeys best practices. Defense in depth is important. We're awhiles off from something that reads your mind and makes your thoughts precise and cogent.

```bash
%%bash
# download and install CBMC
wget https://github.com/diffblue/cbmc/releases/download/cbmc-5.95.1/ubuntu-20.04-cbmc-5.95.1-Linux.deb
apt-get install bash-completion
dpkg -i ubuntu-20.04-cbmc-5.95.1-Linux.deb
```

```python
! cbmc /tmp/ex1.c
```

    CBMC version 5.95.1 (cbmc-5.95.1) 64-bit x86_64 linux
    Parsing /tmp/ex1.c
    Converting
    Type-checking ex1
    Generating GOTO Program
    Adding CPROVER library (x86_64)
    Removal of function pointers and virtual functions
    Generic Property Instrumentation
    Running with 8 object bits, 56 offset bits (default)
    Starting Bounded Model Checking
    Runtime Symex: 0.00265417s
    size of program expression: 23 steps
    simple slicing removed 5 assignments
    Generated 1 VCC(s), 1 remaining after simplification
    Runtime Postprocess Equation: 1.2691e-05s
    Passing problem to propositional reduction
    converting SSA
    Runtime Convert SSA: 0.0010266s
    Running propositional reduction
    Post-processing
    Runtime Post-process: 4.841e-06s
    Solving with MiniSAT 2.2.1 with simplifier
    67 variables, 100 clauses
    SAT checker inconsistent: instance is UNSATISFIABLE
    Runtime Solver: 1.542e-05s
    Runtime decision procedure: 0.0014064s
    
    ** Results:
    /tmp/ex1.c function main
    [2m[main.assertion.1] [0mline 5 assertion x != 12345: [32mSUCCESS[0m
    
    ** 0 of 1 failed (1 iterations)
    VERIFICATION SUCCESSFUL

It was commented that your compiler's `-Wall -Wextra -Wpedantic` can check this issue. It is good to enable and deal with all warnings somehow. Indeed, this program is obviously suspicious. These checks will not catch all problems and cannot catch some things CBMC can.

```python
! gcc -Wall -Wextra -Wpedantic /tmp/ex1.c -o /tmp/ex1 -fdiagnostics-plain-output
```

    [01m[K/tmp/ex1.c:[m[K In function ‘[01m[Kmain[m[K’:
    [01m[K/tmp/ex1.c:4:8:[m[K [01;35m[Kwarning: [m[K‘[01m[Kx[m[K’ is used uninitialized [[01;35m[K]8;;https://gcc.gnu.org/onlinedocs/gcc/Warning-Options.html#index-Wuninitialized-Wuninitialized]8;;[m[K]
        4 |     if [01;35m[K([m[Kx <= 42){
          |        [01;35m[K^[m[K

Another interesting tool to sort of spread spectrum apply static analyses to projects is [CodeChecker](https://codechecker.readthedocs.io/en/latest/). This applies some lighter weight larger scale analyses like [cppcheck](https://cppcheck.sourceforge.io/), infer, and the compiler built in analyzers. It also makes nice little html pages and has some kind of CI story.

These are good things to run. Coming back clean is no guarantee of software quality, but it is a good sign.

```python
! python3 pip install codechecker #install codechecker
```

```python
! CodeChecker check --build "clang /tmp/ex1.c"
```

    [INFO 2024-02-05 15:26] - Starting build...
    [INFO 2024-02-05 15:26] - Using CodeChecker ld-logger.
    [INFO 2024-02-05 15:26] - Build finished successfully.
    [INFO 2024-02-05 15:26] - Previous analysis results in '/tmp/tmpc7xy9pwi' have been removed, overwriting with current result
    [INFO 2024-02-05 15:27] - Enabled checkers:
    clangsa: alpha.security.cert.pos.34c, core.BitwiseShift, core.CallAndMessage, core.DivideZero, core.NonNullParamChecker, core.NullDereference, core.StackAddressEscape, core.UndefinedBinaryOperatorResult, core.VLASize, core.uninitialized.ArraySubscript, core.uninitialized.Assign, core.uninitialized.Branch, core.uninitialized.CapturedBlockVariable, core.uninitialized.NewArraySize, core.uninitialized.UndefReturn, cplusplus.InnerPointer, cplusplus.Move, cplusplus.NewDelete, cplusplus.NewDeleteLeaks, cplusplus.PlacementNew, cplusplus.PureVirtualCall, cplusplus.StringChecker, deadcode.DeadStores, nullability.NullPassedToNonnull, nullability.NullReturnedFromNonnull, optin.cplusplus.UninitializedObject, optin.cplusplus.VirtualCall, optin.portability.UnixAPI, security.cert.env.InvalidPtr, security.FloatLoopCounter, security.insecureAPI.UncheckedReturn, security.insecureAPI.getpw, security.insecureAPI.gets, security.insecureAPI.mkstemp, security.insecureAPI.mktemp, security.insecureAPI.rand, security.insecureAPI.vfork, unix.API, unix.Malloc, unix.MallocSizeof, unix.MismatchedDeallocator, unix.StdCLibraryFunctions, unix.Vfork, unix.cstring.BadSizeArg, unix.cstring.NullArg, valist.CopyToSelf, valist.Uninitialized, valist.Unterminated
    cppcheck: cppcheck-IOWithoutPositioning, cppcheck-StlMissingComparison, cppcheck-accessForwarded, cppcheck-accessMoved, cppcheck-argumentSize, cppcheck-arrayIndexOutOfBounds, cppcheck-arrayIndexOutOfBoundsCond, cppcheck-assertWithSideEffect, cppcheck-assignBoolToPointer, cppcheck-assignmentInAssert, cppcheck-autoVariables, cppcheck-autovarInvalidDeallocation, cppcheck-badBitmaskCheck, cppcheck-boostForeachError, cppcheck-bufferAccessOutOfBounds, cppcheck-charBitOp, cppcheck-charLiteralWithCharPtrCompare, cppcheck-checkCastIntToCharAndBack, cppcheck-clarifyStatement, cppcheck-compareBoolExpressionWithInt, cppcheck-comparePointers, cppcheck-comparisonFunctionIsAlwaysTrueOrFalse, cppcheck-comparisonOfBoolWithInvalidComparator, cppcheck-constStatement, cppcheck-containerOutOfBounds, cppcheck-copyCtorAndEqOperator, cppcheck-copyCtorPointerCopying, cppcheck-coutCerrMisusage, cppcheck-danglingLifetime, cppcheck-danglingReference, cppcheck-danglingTemporaryLifetime, cppcheck-deallocDealloc, cppcheck-deallocret, cppcheck-deallocuse, cppcheck-derefInvalidIterator, cppcheck-divideSizeof, cppcheck-doubleFree, cppcheck-duplInheritedMember, cppcheck-eraseDereference, cppcheck-exceptDeallocThrow, cppcheck-exceptThrowInDestructor, cppcheck-floatConversionOverflow, cppcheck-funcArgOrderDifferent, cppcheck-identicalConditionAfterEarlyExit, cppcheck-identicalInnerCondition, cppcheck-ignoredReturnValue, cppcheck-incompatibleFileOpen, cppcheck-incompleteArrayFill, cppcheck-incorrectCharBooleanError, cppcheck-incorrectLogicOperator, cppcheck-incorrectStringBooleanError, cppcheck-incorrectStringCompare, cppcheck-integerOverflow, cppcheck-invalidContainerLoop, cppcheck-invalidContainer, cppcheck-invalidFree, cppcheck-invalidFunctionArg, cppcheck-invalidFunctionArgBool, cppcheck-invalidFunctionArgStr, cppcheck-invalidIterator1, cppcheck-invalidLengthModifierError, cppcheck-invalidLifetime, cppcheck-invalidPrintfArgType_float, cppcheck-invalidPrintfArgType_n, cppcheck-invalidPrintfArgType_p, cppcheck-invalidPrintfArgType_s, cppcheck-invalidPrintfArgType_sint, cppcheck-invalidPrintfArgType_uint, cppcheck-invalidScanfArgType_float, cppcheck-invalidScanfArgType_int, cppcheck-invalidScanfArgType_s, cppcheck-invalidScanfFormatWidth, cppcheck-invalidScanfFormatWidth_smaller, cppcheck-invalidTestForOverflow, cppcheck-invalidscanf, cppcheck-iterators1, cppcheck-iterators2, cppcheck-iterators3, cppcheck-iteratorsCmp1, cppcheck-iteratorsCmp2, cppcheck-leakNoVarFunctionCall, cppcheck-leakReturnValNotUsed, cppcheck-leakUnsafeArgAlloc, cppcheck-literalWithCharPtrCompare, cppcheck-mallocOnClassError, cppcheck-mallocOnClassWarning, cppcheck-memleak, cppcheck-memleakOnRealloc, cppcheck-memsetClass, cppcheck-memsetClassFloat, cppcheck-memsetClassReference, cppcheck-memsetValueOutOfRange, cppcheck-memsetZeroBytes, cppcheck-mismatchAllocDealloc, cppcheck-mismatchSize, cppcheck-mismatchingContainerExpression, cppcheck-mismatchingContainers, cppcheck-missingMemberCopy, cppcheck-missingReturn, cppcheck-moduloAlwaysTrueFalse, cppcheck-multiplySizeof, cppcheck-negativeArraySize, cppcheck-negativeContainerIndex, cppcheck-negativeIndex, cppcheck-negativeMemoryAllocationSize, cppcheck-noCopyConstructor, cppcheck-noDestructor, cppcheck-noOperatorEq, cppcheck-nullPointer, cppcheck-nullPointerArithmetic, cppcheck-nullPointerArithmeticRedundantCheck, cppcheck-nullPointerDefaultArg, cppcheck-nullPointerRedundantCheck, cppcheck-objectIndex, cppcheck-operatorEqMissingReturnStatement, cppcheck-operatorEqToSelf, cppcheck-operatorEqVarError, cppcheck-oppositeInnerCondition, cppcheck-overlappingStrcmp, cppcheck-overlappingWriteFunction, cppcheck-overlappingWriteUnion, cppcheck-pointerAdditionResultNotNull, cppcheck-pointerArithBool, cppcheck-pointerSize, cppcheck-publicAllocationError, cppcheck-pureVirtualCall, cppcheck-raceAfterInterlockedDecrement, cppcheck-readWriteOnlyFile, cppcheck-redundantAssignInSwitch, cppcheck-redundantBitwiseOperationInSwitch, cppcheck-redundantCopyInSwitch, cppcheck-resourceLeak, cppcheck-rethrowNoCurrentException, cppcheck-returnAddressOfAutoVariable, cppcheck-returnAddressOfFunctionParameter, cppcheck-returnDanglingLifetime, cppcheck-returnLocalVariable, cppcheck-returnReference, cppcheck-returnTempReference, cppcheck-seekOnAppendedFile, cppcheck-selfAssignment, cppcheck-selfInitialization, cppcheck-shiftNegativeLHS, cppcheck-shiftNegative, cppcheck-shiftTooManyBits, cppcheck-shiftTooManyBitsSigned, cppcheck-signConversion, cppcheck-signedCharArrayIndex, cppcheck-sizeofCalculation, cppcheck-sizeofDivisionMemfunc, cppcheck-sizeofFunctionCall, cppcheck-sizeofsizeof, cppcheck-sizeofwithnumericparameter, cppcheck-sizeofwithsilentarraypointer, cppcheck-sprintfOverlappingData, cppcheck-staticStringCompare, cppcheck-stlBoundaries, cppcheck-stlIfFind, cppcheck-stlOutOfBounds, cppcheck-stlcstr, cppcheck-stlcstrReturn, cppcheck-stlcstrParam, cppcheck-stlcstrthrow, cppcheck-strPlusChar, cppcheck-stringCompare, cppcheck-stringLiteralWrite, cppcheck-suspiciousCase, cppcheck-suspiciousSemicolon, cppcheck-thisSubtraction, cppcheck-throwInNoexceptFunction, cppcheck-uninitDerivedMemberVar, cppcheck-uninitDerivedMemberVarPrivate, cppcheck-uninitMemberVar, cppcheck-uninitMemberVarPrivate, cppcheck-uninitStructMember, cppcheck-uninitdata, cppcheck-uninitstring, cppcheck-uninitvar, cppcheck-unknownEvaluationOrder, cppcheck-unsafeClassRefMember, cppcheck-unusedLabelSwitch, cppcheck-unusedLabelSwitchConfiguration, cppcheck-useClosedFile, cppcheck-uselessAssignmentPtrArg, cppcheck-uselessCallsCompare, cppcheck-uselessCallsEmpty, cppcheck-uselessCallsRemove, cppcheck-va_end_missing, cppcheck-va_list_usedBeforeStarted, cppcheck-va_start_referencePassed, cppcheck-va_start_subsequentCalls, cppcheck-va_start_wrongParameter, cppcheck-virtualCallInConstructor, cppcheck-virtualDestructor, cppcheck-writeReadOnlyFile, cppcheck-wrongPipeParameterSize, cppcheck-wrongPrintfScanfArgNum, cppcheck-wrongPrintfScanfParameterPositionError, cppcheck-wrongmathcall, cppcheck-zerodiv, cppcheck-zerodivcond
    clang-tidy: bugprone-assert-side-effect, bugprone-bool-pointer-implicit-conversion, bugprone-compare-pointer-to-member-virtual-function, bugprone-copy-constructor-init, bugprone-dangling-handle, bugprone-dynamic-static-initializers, bugprone-fold-init-type, bugprone-forward-declaration-namespace, bugprone-forwarding-reference-overload, bugprone-inaccurate-erase, bugprone-inc-dec-in-conditions, bugprone-incorrect-enable-if, bugprone-incorrect-roundings, bugprone-infinite-loop, bugprone-integer-division, bugprone-lambda-function-name, bugprone-macro-repeated-side-effects, bugprone-misplaced-operator-in-strlen-in-alloc, bugprone-misplaced-pointer-arithmetic-in-alloc, bugprone-misplaced-widening-cast, bugprone-move-forwarding-reference, bugprone-multiple-new-in-one-expression, bugprone-not-null-terminated-result, bugprone-optional-value-conversion, bugprone-shared-ptr-array-mismatch, bugprone-signal-handler, bugprone-signed-char-misuse, bugprone-sizeof-container, bugprone-sizeof-expression, bugprone-standalone-empty, bugprone-string-constructor, bugprone-stringview-nullptr, bugprone-string-literal-with-embedded-nul, bugprone-suspicious-enum-usage, bugprone-suspicious-memory-comparison, bugprone-suspicious-memset-usage, bugprone-suspicious-missing-comma, bugprone-suspicious-realloc-usage, bugprone-suspicious-semicolon, bugprone-swapped-arguments, bugprone-switch-missing-default-case, bugprone-terminating-continue, bugprone-throw-keyword-missing, bugprone-too-small-loop-variable, bugprone-undefined-memory-manipulation, bugprone-undelegated-constructor, bugprone-unhandled-exception-at-new, bugprone-unique-ptr-array-mismatch, bugprone-unused-raii, bugprone-unused-return-value, bugprone-use-after-move, bugprone-virtual-near-miss, cert-dcl54-cpp, cert-dcl58-cpp, cert-dcl59-cpp, cert-err09-cpp, cert-fio38-c, cert-mem57-cpp, cert-oop11-cpp, cert-oop58-cpp, cert-pos44-c, cert-pos47-c, clang-diagnostic-array-bounds-pointer-arithmetic, clang-diagnostic-bitwise-conditional-parentheses, clang-diagnostic-bitwise-instead-of-logical, clang-diagnostic-bitwise-op-parentheses, clang-diagnostic-bool-operation, clang-diagnostic-cast-of-sel-type, clang-diagnostic-char-subscripts, clang-diagnostic-comment, clang-diagnostic-comments, clang-diagnostic-dangling-else, clang-diagnostic-delete-abstract-non-virtual-dtor, clang-diagnostic-delete-non-abstract-non-virtual-dtor, clang-diagnostic-delete-non-virtual-dtor, clang-diagnostic-deprecated-copy, clang-diagnostic-deprecated-copy-with-dtor, clang-diagnostic-deprecated-copy-with-user-provided-dtor, clang-diagnostic-deprecated-copy-dtor, clang-diagnostic-deprecated-copy-with-user-provided-copy, clang-diagnostic-division-by-zero, clang-diagnostic-double-promotion, clang-diagnostic-embedded-directive, clang-diagnostic-empty-init-stmt, clang-diagnostic-extern-c-compat, clang-diagnostic-float-conversion, clang-diagnostic-for-loop-analysis, clang-diagnostic-format, clang-diagnostic-format-overflow, clang-diagnostic-format-overflow-non-kprintf, clang-diagnostic-format-truncation, clang-diagnostic-format-truncation-non-kprintf, clang-diagnostic-format-non-iso, clang-diagnostic-format-pedantic, clang-diagnostic-format-type-confusion, clang-diagnostic-format=2, clang-diagnostic-format-extra-args, clang-diagnostic-format-insufficient-args, clang-diagnostic-format-invalid-specifier, clang-diagnostic-format-nonliteral, clang-diagnostic-format-security, clang-diagnostic-format-y2k, clang-diagnostic-format-zero-length, clang-diagnostic-frame-address, clang-diagnostic-fuse-ld-path, clang-diagnostic-ignored-qualifiers, clang-diagnostic-ignored-reference-qualifiers, clang-diagnostic-implicit, clang-diagnostic-implicit-atomic-properties, clang-diagnostic-implicit-conversion-floating-point-to-bool, clang-diagnostic-implicit-exception-spec-mismatch, clang-diagnostic-implicit-fallthrough, clang-diagnostic-implicit-fallthrough-per-function, clang-diagnostic-implicit-fixed-point-conversion, clang-diagnostic-implicit-retain-self, clang-diagnostic-implicitly-unsigned-literal, clang-diagnostic-implicit-float-conversion, clang-diagnostic-implicit-const-int-float-conversion, clang-diagnostic-implicit-function-declaration, clang-diagnostic-implicit-int, clang-diagnostic-implicit-int-conversion, clang-diagnostic-implicit-int-float-conversion, clang-diagnostic-infinite-recursion, clang-diagnostic-initializer-overrides, clang-diagnostic-int-in-bool-context, clang-diagnostic-logical-not-parentheses, clang-diagnostic-logical-op-parentheses, clang-diagnostic-misleading-indentation, clang-diagnostic-mismatched-tags, clang-diagnostic-missing-braces, clang-diagnostic-missing-field-initializers, clang-diagnostic-missing-method-return-type, clang-diagnostic-most, clang-diagnostic-move, clang-diagnostic-multichar, clang-diagnostic-non-virtual-dtor, clang-diagnostic-nonnull, clang-diagnostic-null-pointer-arithmetic, clang-diagnostic-null-pointer-subtraction, clang-diagnostic-objc-designated-initializers, clang-diagnostic-objc-flexible-array, clang-diagnostic-objc-missing-super-calls, clang-diagnostic-overloaded-shift-op-parentheses, clang-diagnostic-overloaded-virtual, clang-diagnostic-parentheses, clang-diagnostic-parentheses-equality, clang-diagnostic-pessimizing-move, clang-diagnostic-potentially-evaluated-expression, clang-diagnostic-private-extern, clang-diagnostic-range-loop-construct, clang-diagnostic-redundant-move, clang-diagnostic-reorder, clang-diagnostic-reorder-ctor, clang-diagnostic-reorder-init-list, clang-diagnostic-return-std-move, clang-diagnostic-return-type, clang-diagnostic-return-type-c-linkage, clang-diagnostic-self-assign, clang-diagnostic-self-assign-field, clang-diagnostic-self-assign-overloaded, clang-diagnostic-self-move, clang-diagnostic-semicolon-before-method-body, clang-diagnostic-shift-op-parentheses, clang-diagnostic-sign-compare, clang-diagnostic-sizeof-array-argument, clang-diagnostic-sizeof-array-decay, clang-diagnostic-sometimes-uninitialized, clang-diagnostic-static-in-inline, clang-diagnostic-static-self-init, clang-diagnostic-string-concatenation, clang-diagnostic-string-plus-int, clang-diagnostic-switch, clang-diagnostic-switch-default, clang-diagnostic-switch-enum, clang-diagnostic-switch-bool, clang-diagnostic-tautological-bitwise-compare, clang-diagnostic-tautological-compare, clang-diagnostic-tautological-constant-compare, clang-diagnostic-tautological-constant-out-of-range-compare, clang-diagnostic-tautological-objc-bool-compare, clang-diagnostic-tautological-overlap-compare, clang-diagnostic-tautological-pointer-compare, clang-diagnostic-tautological-undefined-compare, clang-diagnostic-trigraphs, clang-diagnostic-unevaluated-expression, clang-diagnostic-uninitialized, clang-diagnostic-uninitialized-const-reference, clang-diagnostic-unknown-pragmas, clang-diagnostic-unneeded-internal-declaration, clang-diagnostic-unused-argument, clang-diagnostic-unused-but-set-parameter, clang-diagnostic-unused-but-set-variable, clang-diagnostic-unused-comparison, clang-diagnostic-unused-const-variable, clang-diagnostic-unused-function, clang-diagnostic-unused-label, clang-diagnostic-unused-lambda-capture, clang-diagnostic-unused-local-typedef, clang-diagnostic-unused-local-typedefs, clang-diagnostic-unused-parameter, clang-diagnostic-unused-private-field, clang-diagnostic-unused-property-ivar, clang-diagnostic-unused-result, clang-diagnostic-unused-value, clang-diagnostic-unused-variable, clang-diagnostic-user-defined-warnings, clang-diagnostic-volatile-register-var, concurrency-thread-canceltype-asynchronous, cppcoreguidelines-avoid-capturing-lambda-coroutines, cppcoreguidelines-avoid-reference-coroutine-parameters, cppcoreguidelines-virtual-class-destructor, google-build-namespaces, misc-confusable-identifiers, misc-definitions-in-headers, misc-header-include-cycle, misc-misleading-bidirectional, misc-misleading-identifier, misc-misplaced-const, misc-redundant-expression, misc-unconventional-assign-operator, misc-uniqueptr-reset-release, performance-inefficient-algorithm, performance-move-const-arg, performance-move-constructor-init, performance-no-automatic-move, performance-noexcept-destructor, performance-noexcept-move-constructor, performance-noexcept-swap, performance-trivially-destructible, readability-container-contains, readability-container-data-pointer, readability-reference-to-constructed-temporary, readability-suspicious-call-argument
    [INFO 2024-02-05 15:27] - Starting static analysis ...
    [INFO 2024-02-05 15:27] - [1/3] cppcheck analyzed ex1.c successfully.
    [INFO 2024-02-05 15:27] - [2/3] clangsa analyzed ex1.c successfully.
    [INFO 2024-02-05 15:27] - [3/3] clang-tidy analyzed ex1.c successfully.
    [INFO 2024-02-05 15:27] - ----==== Summary ====----
    [INFO 2024-02-05 15:27] - Successfully analyzed
    [INFO 2024-02-05 15:27] -   clangsa: 1
    [INFO 2024-02-05 15:27] -   cppcheck: 1
    [INFO 2024-02-05 15:27] -   clang-tidy: 1
    [INFO 2024-02-05 15:27] - Total analyzed compilation commands: 1
    [INFO 2024-02-05 15:27] - ----=================----
    [INFO 2024-02-05 15:27] - Analysis finished.
    [INFO 2024-02-05 15:27] - To view results in the terminal use the "CodeChecker parse" command.
    [INFO 2024-02-05 15:27] - To store results use the "CodeChecker store" command.
    [INFO 2024-02-05 15:27] - See --help and the user guide for further options about parsing and storing the reports.
    [INFO 2024-02-05 15:27] - ----=================----
    [INFO 2024-02-05 15:27] - Analysis length: 0.45849108695983887 sec.
    [WARNING 2024-02-05 15:27] - Analyzer 'gcc' is enabled but CodeChecker is failed to execute analysis with it: 'Incompatible version: GCC binary found is too old at v11.4.0; minimum version is 13.0.0. Maybe try setting an absolute path to a different analyzer binary via the env variable CC_ANALYZER_BIN?'. Please check your 'PATH' environment variable and the 'config/package_layout.json' file!
    [HIGH] /tmp/ex1.c:4:11: The left operand of '<=' is a garbage value [core.UndefinedBinaryOperatorResult]
        if (x <= 42){
              ^
    
    Found 1 defect(s) in ex1.c
    
    [HIGH] /tmp/ex1.c:4:9: Uninitialized variable: x [cppcheck-uninitvar]
        if (x <= 42){
            ^
    
    Found 1 defect(s) in ex1.c
    
    [MEDIUM] /tmp/ex1.c:4:9: variable 'x' is uninitialized when used here [clang-diagnostic-uninitialized]
        if (x <= 42){
            ^
    
    Found 1 defect(s) in ex1.c
    
    
    ----==== Severity Statistics ====----
    ----------------------------
    Severity | Number of reports
    ----------------------------
    HIGH     |                 2
    MEDIUM   |                 1
    ----------------------------
    ----=================----
    
    ----==== Checker Statistics ====----
    -----------------------------------------------------------------
    Checker name                       | Severity | Number of reports
    -----------------------------------------------------------------
    core.UndefinedBinaryOperatorResult | HIGH     |                 1
    cppcheck-uninitvar                 | HIGH     |                 1
    clang-diagnostic-uninitialized     | MEDIUM   |                 1
    -----------------------------------------------------------------
    ----=================----
    
    ----==== File Statistics ====----
    -----------------------------
    File name | Number of reports
    -----------------------------
    ex1.c     |                 3
    -----------------------------
    ----=================----
    
    ----======== Summary ========----
    ---------------------------------------------
    Number of processed analyzer result files | 3
    Number of analyzer reports                | 3
    ---------------------------------------------
    ----=================----

I am still suspicious of the exact truth on whether the example given is actually undefined behavior. I mentioned a couple tools for checking on undefined behavior. Here I'll try the [undefined behavior sanitizer](https://clang.llvm.org/docs/UndefinedBehaviorSanitizer.html) which comes with your compiler and the [Cerberus](https://www.cl.cam.ac.uk/~pes20/cerberus/) interpreter. The UBSanitizer injects runtime checks for undefined behavior happening. I am unsure how complete these checks are or whther they can be optimized away. They probably try to make sure they are as reliable as is possible.

The UB sanitizer does not take issue with this example, nor does cerberus. Curious.

```python
! clang -fsanitize=undefined /tmp/ex1.c -o /tmp/ex1 && /tmp/ex1
```

```bash
%%bash
# install cerberus. This needs to get ocaml first. Might take a bit
apt install opam
opam init -y
eval $(opam env)
git clone https://github.com/rems-project/cerberus.git
cd cerberus
apt-get install libgmp-dev
opam install -y --deps-only ./cerberus-lib.opam ./cerberus.opam
make
```

```python
! cerberus --exec /tmp/ex1.c
```

Just to check that it isn't compiling away.

```python
! objdump /tmp/ex1 -d | grep -A 20 main.:
```

    000000000002ea38 <main>:
       2ea38: 55                    push   %rbp
       2ea39: 48 89 e5              mov    %rsp,%rbp
       2ea3c: 48 83 ec 10           sub    $0x10,%rsp
       2ea40: c7 45 fc 00 00 00 00  movl   $0x0,-0x4(%rbp)
       2ea47: 83 7d f8 2a           cmpl   $0x2a,-0x8(%rbp)
       2ea4b: 0f 8f 4c 00 00 00     jg     2ea9d <main+0x65>
       2ea51: 81 7d f8 39 30 00 00  cmpl   $0x3039,-0x8(%rbp)
       2ea58: 0f 84 05 00 00 00     je     2ea63 <main+0x2b>
       2ea5e: e9 35 00 00 00        jmp    2ea98 <main+0x60>
       2ea63: 48 8d 3d c1 92 00 00  lea    0x92c1(%rip),%rdi        # 37d2b <_ZL10kVptrCheck+0xf25>
       2ea6a: 48 8d 35 c5 92 00 00  lea    0x92c5(%rip),%rsi        # 37d36 <_ZL10kVptrCheck+0xf30>
       2ea71: ba 05 00 00 00        mov    $0x5,%edx
       2ea76: 48 8d 0d c4 92 00 00  lea    0x92c4(%rip),%rcx        # 37d41 <_ZL10kVptrCheck+0xf3b>
       2ea7d: e8 4e 66 fd ff        call   50d0 <__assert_fail@plt>
       2ea82: 31 c0                 xor    %eax,%eax
       2ea84: a8 01                 test   $0x1,%al
       2ea86: 0f 85 0c 00 00 00     jne    2ea98 <main+0x60>
       2ea8c: 48 8d 3d d5 80 01 00  lea    0x180d5(%rip),%rdi        # 46b68 <_ZL17kSuppressionTypes+0x128>
       2ea93: e8 08 d1 ff ff        call   2bba0 <__ubsan_handle_builtin_unreachable>
       2ea98: e9 00 00 00 00        jmp    2ea9d <main+0x65>

Asserts that aren't triggering may be an odd case, so let's do something more straightforward: printing uninitialized values.

```python
%%file /tmp/ex2.c
#include <stdio.h>
int main(){
    int x;
    printf("Value of x: %d\n", x);
}
```

    Overwriting /tmp/ex2.c

The UB sanitizer still does not take issue.
Cerberus thinks this is unspecified behavior (which prints differently from undefined behavior)

```python
! clang -fsanitize=undefined /tmp/ex2.c -o /tmp/ex2 && /tmp/ex2
```

    Value of x: 0

```python
! cerberus --exec /tmp/ex2.c
```

    Value of x: UNSPEC

This slightly different program is however, quite bad. An uninitialized pointer is dereferenced and both methods complain accordingly.

```python
%%file /tmp/ex3.c
#include <stdio.h>
int main(){
    int* x;
    printf("Value of x: %d\n", *x);
}
```

    Overwriting /tmp/ex3.c

```python
! clang -fsanitize=undefined /tmp/ex3.c -o /tmp/ex3 && /tmp/ex3
```

    [1m/tmp/ex3.c:4:32:[1m[31m runtime error: [1m[0m[1mload of null pointer of type 'int'[1m[0m
    SUMMARY: UndefinedBehaviorSanitizer: undefined-behavior /tmp/ex3.c:4:32 
    UndefinedBehaviorSanitizer:DEADLYSIGNAL
    [1m[31m==33249==ERROR: UndefinedBehaviorSanitizer: SEGV on unknown address 0x000000000000 (pc 0x563890a65a7f bp 0x7ffde3c0d8b0 sp 0x7ffde3c0d890 T33249)
    [1m[0m==33249==The signal is caused by a READ memory access.
    ==33249==Hint: address points to the zero page.
        #0 0x563890a65a7f in main (/tmp/ex3+0x2ea7f) (BuildId: c9aba5b3a42c58e96d9e5e92c81c7a22b892dcf2)
        #1 0x7f73eb0abd8f in __libc_start_call_main csu/../sysdeps/nptl/libc_start_call_main.h:58:16
        #2 0x7f73eb0abe3f in __libc_start_main csu/../csu/libc-start.c:392:3
        #3 0x563890a3c3e4 in _start (/tmp/ex3+0x53e4) (BuildId: c9aba5b3a42c58e96d9e5e92c81c7a22b892dcf2)
    
    UndefinedBehaviorSanitizer can not provide additional info.
    SUMMARY: UndefinedBehaviorSanitizer: SEGV (/tmp/ex3+0x2ea7f) (BuildId: c9aba5b3a42c58e96d9e5e92c81c7a22b892dcf2) in main
    ==33249==ABORTING

```python
! cerberus --exec /tmp/ex3.c
```

    [1m/tmp/ex3.c:4:32:[0m [1;31merror:[0m [1m[1mundefined behaviour: [0mthe operand of the unary '*' operator has an invalid value[0m
        printf("Value of x: %d\n", *x);
    [1;32m                               ^~ [0m
    [1m§6.5.3.2#4, sentence 4[0m: 
    4   The unary * operator denotes indirection. If the operand points to a function, the result is
        a function designator; if it points to an object, the result is an lvalue designating the
        object. If the operand has type ``pointer to type'', the result has type ``type''. If an
        invalid value has been assigned to the pointer, the behavior of the unary * operator is
        undefined.102)
        Forward references: storage-class specifiers (6.7.1), structure and union specifiers
        (6.7.2.1).

# Bits and Bobbles

I am not an expert in undefined behavior. Take anything you read here with a grain of salt. (Honestly, take anything you read anywhere on this topic with a grain of salt. People say of a lot of confident wrong stuff.) This represents my best guess at the topic, using the best tools i know of.

First off, you don't have to be _that_ scared. A mistake about undefined behavior is an unlikely cause of death. We are more likely to get cancer from some kind of slovenly corporate oversight about deodorant ingredients or basking in the wrong sunbeam.

We all die some day anyway. It is hopefully a whiles off and hopefully won't be that horrifying or painful.

On the other hand, I would nearly guarantee C and C++ are in the bioweapon, medical radiation, and nuclear stack. So it only takes one real nasty bug or even misconception to kill us all.

Turn on s lot of [warnings](https://gcc.gnu.org/onlinedocs/gcc/Warning-Options.html) (`-Wall -Wextra -Wpedantic` is a start) when you are working in an unsafe language and deal with them. In principle, it is quite possible for the compiler to detect situations that humans are likely to be confused. It isn't perfect, but even precise language lawyering isn't perfect if it doesn't comply with this particular user's intuitions and intent.

A true Achilles heal of all modelling and verification tools is the connection of the model back to physical reality or the mushy concept of human intent. A model or verification or optimization is only as good as it's weakest link.

I do not have (and suspect there cannot be) a final satisfying answer to this problem.

I also do not consider it to be a a complete demonstration of the futility or uselessness of checking of verification attempts.

<https://en.wikipedia.org/wiki/Undefined_behavior>

Here's my basic understanding of the distinction between undefine, unspecified, and implementation defined behavior.

Undefined behavior:
An imperative program is kind of like a `state -> state` function. If you were to write an interpreter of your target imperative language in a purely functional style, this comes very naturally. The interpreter has a type `program -> state -> state` and if you partially apply it, you get it's state transformer semantics. `x := x + 1;` gets parsed as something like `Assign("x", Plus(Var("x"), Lit(1))`.   It takes in an initial state, which is the value of variables and memory, and outputs a final state of new values of variables and memory. blahblahblahblah

unspecified behavior:
If the program is allowed to fail, then the final state is not defined. Then we can model programs as `state -> option state`.

implementation defined behavior:
A different thing programs can do is do something, but it can be kind of random. This is unspecified behavior. Programs can be different choices of order of operations. We can think of programs as `state -> list state` with a list of possible final states.
A slightly different notion is that programs can be implementation-defined. They still do something that isn't quite clear, but the implementation picks a consistent thing to do. We can model this purely functionally.
`() -> option state`

It is not always obvious in unsafe languages where the boundary between totally well-defined, undefined, unspecified, and implementation defined.

I am also suspicious that many of the HN comments are not right. People will talk at great length about undefined behavior. It was claimed that this example is an instance of "undefined behavior". I believe that this may be (or perhaps should be) an instance of "unspecified behavior', a distinct and slightly less insidious cousin. If so, CBMC is treating it's emulation of unspecified behavior in fairly reasonably manner I believe.

See for example 2.6.1 <https://robbertkrebbers.nl/research/thesis.pdf>  Defect Report #260  <https://www.open-std.org/jtc1/sc22/wg14/www/docs/dr_260.htm> Defect Report is numbered #451 <https://www.open-std.org/jtc1/sc22/wg14/www/docs/dr_451.htm>

I may be just confusing the issue because I hate being shown to be wrong and ignorant on the internet by strangers. Could be. Could be.

John Regehr has many great blog posts around this an other topics
<https://blog.regehr.org/archives/1234>

This is not the whole story, maybe not even a _majority_ of the story. What is the difference between a "do nothing" program and one that prints `"Hello World`? In our current conception of state, it is not clear that printing is evident in final state. There are a couple of ways out of this. We could attempt to say that no no no, state is the entire _universe_ including our eyeballs and the screen. This is slightly actionable. but also a bit silly.
We could also abandon our entire conception of imperative programs as mathematical functions. This is a weird way to think about it for most of the population, and smacks of sophistry and great faith and love of traditional mathematics. Traditional mathematics _is_  the prime example of being complex and yet (varying degrees of) precise.
The other thing we can do is say that there is

The C and C++ standards. I have not mastered the art of reading these (yea, yea go ahead and rip into me, you jackals.). C11 <https://port70.net/~nsz/c/c11/n1570.html#J>

Also take a look at the [Compcert](https://compcert.org/) [Formal verification of a realistic compiler](https://xavierleroy.org/publi/compcert-CACM.pdf) [A formally verified compiler back-end](https://xavierleroy.org/publi/compcert-backend.pdf),

C semantics

- The C standard formalized in Coq <https://robbertkrebbers.nl/research/thesis.pdf>
- K framework semantics <https://github.com/kframework/c-semantics> <https://www.ideals.illinois.edu/items/34571>
- <https://www.cl.cam.ac.uk/~pes20/cerberus/> cerberus

 <https://www.cis.upenn.edu/~stevez/papers/XZHH+20.pdf> interaction trees. Algerbaic effect style modeling

 memory model semantics.

```bash
%%bash
# various installations
#pip install codechecker
#apt install cppcheck
# face book infer
#VERSION=1.1.0; \
#curl -sSL "https://github.com/facebook/infer/releases/download/v$VERSION/infer-linux64-v$VERSION.tar.xz" \
#| sudo tar -C /opt -xJ && \
#sudo ln -s "/opt/infer-linux64-v$VERSION/bin/infer" /usr/local/bin/infer
# cerberus


```

<https://news.ycombinator.com/item?id=39191507>

-Wall -Wpedantic -Wextra -Werror

For undefined behavior detection, I have heard of these:

- UB sanitizer <https://clang.llvm.org/docs/UndefinedBehaviorSanitizer.html> this can be used with klee for more coverage, but that doesn't increase the UB

- Cerberus Semantics <https://www.cl.cam.ac.uk/~pes20/cerberus/>

- <https://github.com/kframework/c-semantics>

- <https://github.com/TrustInSoft/tis-interpreter>

<https://wordsandbuttons.online/so_you_think_you_know_c.html>

<https://clang-analyzer.llvm.org/>
<https://codechecker.readthedocs.io/en/latest/>
<https://clang-analyzer.llvm.org/scan-build.html>

<https://stackoverflow.com/questions/7237963/is-there-a-c-implementation-that-detects-all-undefined-behavior>

<https://twitter.com/kees_cook/status/1588007082288353281?s=20&t=udFq9u7zLY-5-Ae6VrdqeQ>

```
-Wall
-D_FORTIFY_SOURCE=2
-fsanitize=bounds fsanitize-undefined-trap-on-error
-fstrict-flex-arrays (GCC 13+, Clang 16+)
```

semgrep
codeql

frama-c

astree

## Clang-tidy
<https://clang.llvm.org/extra/clang-tidy/>

```python
! clang-tidy /tmp/ex1.c
```

```python
%%file /tmp/ub.c
#include <assert.h>
#include <stdio.h>
int main(){
    int x;
    x++;
    printf("Value of x: %d\n", x);
    //int y = *(int *)NULL;
    //assert(x != 12345);
    //assert(1 == 0);
}
```

    Overwriting /tmp/ub.c

```python
! gcc -O3 -Wall -Wpedantic -Wextra  /tmp/ub.c -o /tmp/ub && /tmp/ub
```

    [01m[K/tmp/ub.c:[m[K In function ‘[01m[Kmain[m[K’:
    [01m[K/tmp/ub.c:5:6:[m[K [01;35m[Kwarning: [m[K‘[01m[Kx[m[K’ is used uninitialized [[01;35m[K]8;;https://gcc.gnu.org/onlinedocs/gcc/Warning-Options.html#index-Wuninitialized-Wuninitialized]8;;[m[K]
        5 |     [01;35m[Kx++[m[K;
          |     [01;35m[K~^~[m[K
    Value of x: 1

```python
! objdump -d /tmp/ub | grep -A 20 main.:
```

    0000000000001060 <main>:
        1060: f3 0f 1e fa           endbr64 
        1064: 48 83 ec 08           sub    $0x8,%rsp
        1068: ba 01 00 00 00        mov    $0x1,%edx
        106d: bf 01 00 00 00        mov    $0x1,%edi
        1072: 31 c0                 xor    %eax,%eax
        1074: 48 8d 35 89 0f 00 00  lea    0xf89(%rip),%rsi        # 2004 <_IO_stdin_used+0x4>
        107b: e8 d0 ff ff ff        call   1050 <__printf_chk@plt>
        1080: 31 c0                 xor    %eax,%eax
        1082: 48 83 c4 08           add    $0x8,%rsp
        1086: c3                    ret    
        1087: 66 0f 1f 84 00 00 00  nopw   0x0(%rax,%rax,1)
        108e: 00 00 
    
    0000000000001090 <_start>:
        1090: f3 0f 1e fa           endbr64 
        1094: 31 ed                 xor    %ebp,%ebp
        1096: 49 89 d1              mov    %rdx,%r9
        1099: 5e                    pop    %rsi
        109a: 48 89 e2              mov    %rsp,%rdx
        109d: 48 83 e4 f0           and    $0xfffffffffffffff0,%rsp

```bash
%%bash
cerberus --exec /tmp/ub.c
#cerberus --batch 
```

    /tmp/ub.c:7:13: error: undefined behaviour: the operand of the unary '*' operator has an invalid value
        int y = *(int *)NULL;
                ^~~~~~~~~~~~~~~~~~~~~~ 
    §6.5.3.2#4, sentence 4: 
    4   The unary * operator denotes indirection. If the operand points to a function, the result is
        a function designator; if it points to an object, the result is an lvalue designating the
        object. If the operand has type ``pointer to type'', the result has type ``type''. If an
        invalid value has been assigned to the pointer, the behavior of the unary * operator is
        undefined.102)
        Forward references: storage-class specifiers (6.7.1), structure and union specifiers
        (6.7.2.1).

## Codechecker
<https://github.com/Ericsson/codechecker>
That compile_commands.json might be kind of interesting

```bash
%%bash
# instrument a build first
CodeChecker log -o /tmp/compile_commands.json --build "clang -o /tmp/ub /tmp/ub.c"
# Then run the analyzer
CodeChecker analyze /tmp/compile_commands.json -o /tmp/reports
CodeChecker parse /tmp/reports -e html -o /tmp/reports.html

# all in one
#CodeChecker check --build "make" --output ./reports --clean \
#    --enable sensitive
```

    [INFO 2024-02-01 11:11] - Starting build...
    [INFO 2024-02-01 11:11] - Using CodeChecker ld-logger.
    [INFO 2024-02-01 11:11] - Build finished successfully.
    [INFO 2024-02-01 11:11] - Enabled checkers:
    clang-tidy: bugprone-assert-side-effect, bugprone-bool-pointer-implicit-conversion, bugprone-compare-pointer-to-member-virtual-function, bugprone-copy-constructor-init, bugprone-dangling-handle, bugprone-dynamic-static-initializers, bugprone-fold-init-type, bugprone-forward-declaration-namespace, bugprone-forwarding-reference-overload, bugprone-inaccurate-erase, bugprone-inc-dec-in-conditions, bugprone-incorrect-enable-if, bugprone-incorrect-roundings, bugprone-infinite-loop, bugprone-integer-division, bugprone-lambda-function-name, bugprone-macro-repeated-side-effects, bugprone-misplaced-operator-in-strlen-in-alloc, bugprone-misplaced-pointer-arithmetic-in-alloc, bugprone-misplaced-widening-cast, bugprone-move-forwarding-reference, bugprone-multiple-new-in-one-expression, bugprone-not-null-terminated-result, bugprone-optional-value-conversion, bugprone-shared-ptr-array-mismatch, bugprone-signal-handler, bugprone-signed-char-misuse, bugprone-sizeof-container, bugprone-sizeof-expression, bugprone-standalone-empty, bugprone-string-constructor, bugprone-stringview-nullptr, bugprone-string-literal-with-embedded-nul, bugprone-suspicious-enum-usage, bugprone-suspicious-memory-comparison, bugprone-suspicious-memset-usage, bugprone-suspicious-missing-comma, bugprone-suspicious-realloc-usage, bugprone-suspicious-semicolon, bugprone-swapped-arguments, bugprone-switch-missing-default-case, bugprone-terminating-continue, bugprone-throw-keyword-missing, bugprone-too-small-loop-variable, bugprone-undefined-memory-manipulation, bugprone-undelegated-constructor, bugprone-unhandled-exception-at-new, bugprone-unique-ptr-array-mismatch, bugprone-unused-raii, bugprone-unused-return-value, bugprone-use-after-move, bugprone-virtual-near-miss, cert-dcl54-cpp, cert-dcl58-cpp, cert-dcl59-cpp, cert-err09-cpp, cert-fio38-c, cert-mem57-cpp, cert-oop11-cpp, cert-oop58-cpp, cert-pos44-c, cert-pos47-c, clang-diagnostic-array-bounds-pointer-arithmetic, clang-diagnostic-bitwise-conditional-parentheses, clang-diagnostic-bitwise-instead-of-logical, clang-diagnostic-bitwise-op-parentheses, clang-diagnostic-bool-operation, clang-diagnostic-cast-of-sel-type, clang-diagnostic-char-subscripts, clang-diagnostic-comment, clang-diagnostic-comments, clang-diagnostic-dangling-else, clang-diagnostic-delete-abstract-non-virtual-dtor, clang-diagnostic-delete-non-abstract-non-virtual-dtor, clang-diagnostic-delete-non-virtual-dtor, clang-diagnostic-deprecated-copy, clang-diagnostic-deprecated-copy-with-dtor, clang-diagnostic-deprecated-copy-with-user-provided-dtor, clang-diagnostic-deprecated-copy-dtor, clang-diagnostic-deprecated-copy-with-user-provided-copy, clang-diagnostic-division-by-zero, clang-diagnostic-double-promotion, clang-diagnostic-embedded-directive, clang-diagnostic-empty-init-stmt, clang-diagnostic-extern-c-compat, clang-diagnostic-float-conversion, clang-diagnostic-for-loop-analysis, clang-diagnostic-format, clang-diagnostic-format-overflow, clang-diagnostic-format-overflow-non-kprintf, clang-diagnostic-format-truncation, clang-diagnostic-format-truncation-non-kprintf, clang-diagnostic-format-non-iso, clang-diagnostic-format-pedantic, clang-diagnostic-format-type-confusion, clang-diagnostic-format=2, clang-diagnostic-format-extra-args, clang-diagnostic-format-insufficient-args, clang-diagnostic-format-invalid-specifier, clang-diagnostic-format-nonliteral, clang-diagnostic-format-security, clang-diagnostic-format-y2k, clang-diagnostic-format-zero-length, clang-diagnostic-frame-address, clang-diagnostic-fuse-ld-path, clang-diagnostic-ignored-qualifiers, clang-diagnostic-ignored-reference-qualifiers, clang-diagnostic-implicit, clang-diagnostic-implicit-atomic-properties, clang-diagnostic-implicit-conversion-floating-point-to-bool, clang-diagnostic-implicit-exception-spec-mismatch, clang-diagnostic-implicit-fallthrough, clang-diagnostic-implicit-fallthrough-per-function, clang-diagnostic-implicit-fixed-point-conversion, clang-diagnostic-implicit-retain-self, clang-diagnostic-implicitly-unsigned-literal, clang-diagnostic-implicit-float-conversion, clang-diagnostic-implicit-const-int-float-conversion, clang-diagnostic-implicit-function-declaration, clang-diagnostic-implicit-int, clang-diagnostic-implicit-int-conversion, clang-diagnostic-implicit-int-float-conversion, clang-diagnostic-infinite-recursion, clang-diagnostic-initializer-overrides, clang-diagnostic-int-in-bool-context, clang-diagnostic-logical-not-parentheses, clang-diagnostic-logical-op-parentheses, clang-diagnostic-misleading-indentation, clang-diagnostic-mismatched-tags, clang-diagnostic-missing-braces, clang-diagnostic-missing-field-initializers, clang-diagnostic-missing-method-return-type, clang-diagnostic-most, clang-diagnostic-move, clang-diagnostic-multichar, clang-diagnostic-non-virtual-dtor, clang-diagnostic-nonnull, clang-diagnostic-null-pointer-arithmetic, clang-diagnostic-null-pointer-subtraction, clang-diagnostic-objc-designated-initializers, clang-diagnostic-objc-flexible-array, clang-diagnostic-objc-missing-super-calls, clang-diagnostic-overloaded-shift-op-parentheses, clang-diagnostic-overloaded-virtual, clang-diagnostic-parentheses, clang-diagnostic-parentheses-equality, clang-diagnostic-pessimizing-move, clang-diagnostic-potentially-evaluated-expression, clang-diagnostic-private-extern, clang-diagnostic-range-loop-construct, clang-diagnostic-redundant-move, clang-diagnostic-reorder, clang-diagnostic-reorder-ctor, clang-diagnostic-reorder-init-list, clang-diagnostic-return-std-move, clang-diagnostic-return-type, clang-diagnostic-return-type-c-linkage, clang-diagnostic-self-assign, clang-diagnostic-self-assign-field, clang-diagnostic-self-assign-overloaded, clang-diagnostic-self-move, clang-diagnostic-semicolon-before-method-body, clang-diagnostic-shift-op-parentheses, clang-diagnostic-sign-compare, clang-diagnostic-sizeof-array-argument, clang-diagnostic-sizeof-array-decay, clang-diagnostic-sometimes-uninitialized, clang-diagnostic-static-in-inline, clang-diagnostic-static-self-init, clang-diagnostic-string-concatenation, clang-diagnostic-string-plus-int, clang-diagnostic-switch, clang-diagnostic-switch-default, clang-diagnostic-switch-enum, clang-diagnostic-switch-bool, clang-diagnostic-tautological-bitwise-compare, clang-diagnostic-tautological-compare, clang-diagnostic-tautological-constant-compare, clang-diagnostic-tautological-constant-out-of-range-compare, clang-diagnostic-tautological-objc-bool-compare, clang-diagnostic-tautological-overlap-compare, clang-diagnostic-tautological-pointer-compare, clang-diagnostic-tautological-undefined-compare, clang-diagnostic-trigraphs, clang-diagnostic-unevaluated-expression, clang-diagnostic-uninitialized, clang-diagnostic-uninitialized-const-reference, clang-diagnostic-unknown-pragmas, clang-diagnostic-unneeded-internal-declaration, clang-diagnostic-unused-argument, clang-diagnostic-unused-but-set-parameter, clang-diagnostic-unused-but-set-variable, clang-diagnostic-unused-comparison, clang-diagnostic-unused-const-variable, clang-diagnostic-unused-function, clang-diagnostic-unused-label, clang-diagnostic-unused-lambda-capture, clang-diagnostic-unused-local-typedef, clang-diagnostic-unused-local-typedefs, clang-diagnostic-unused-parameter, clang-diagnostic-unused-private-field, clang-diagnostic-unused-property-ivar, clang-diagnostic-unused-result, clang-diagnostic-unused-value, clang-diagnostic-unused-variable, clang-diagnostic-user-defined-warnings, clang-diagnostic-volatile-register-var, concurrency-thread-canceltype-asynchronous, cppcoreguidelines-avoid-capturing-lambda-coroutines, cppcoreguidelines-avoid-reference-coroutine-parameters, cppcoreguidelines-virtual-class-destructor, google-build-namespaces, misc-confusable-identifiers, misc-definitions-in-headers, misc-header-include-cycle, misc-misleading-bidirectional, misc-misleading-identifier, misc-misplaced-const, misc-redundant-expression, misc-unconventional-assign-operator, misc-uniqueptr-reset-release, performance-inefficient-algorithm, performance-move-const-arg, performance-move-constructor-init, performance-no-automatic-move, performance-noexcept-destructor, performance-noexcept-move-constructor, performance-noexcept-swap, performance-trivially-destructible, readability-container-contains, readability-container-data-pointer, readability-reference-to-constructed-temporary, readability-suspicious-call-argument
    clangsa: alpha.security.cert.pos.34c, core.BitwiseShift, core.CallAndMessage, core.DivideZero, core.NonNullParamChecker, core.NullDereference, core.StackAddressEscape, core.UndefinedBinaryOperatorResult, core.VLASize, core.uninitialized.ArraySubscript, core.uninitialized.Assign, core.uninitialized.Branch, core.uninitialized.CapturedBlockVariable, core.uninitialized.NewArraySize, core.uninitialized.UndefReturn, cplusplus.InnerPointer, cplusplus.Move, cplusplus.NewDelete, cplusplus.NewDeleteLeaks, cplusplus.PlacementNew, cplusplus.PureVirtualCall, cplusplus.StringChecker, deadcode.DeadStores, nullability.NullPassedToNonnull, nullability.NullReturnedFromNonnull, optin.cplusplus.UninitializedObject, optin.cplusplus.VirtualCall, optin.portability.UnixAPI, security.cert.env.InvalidPtr, security.FloatLoopCounter, security.insecureAPI.UncheckedReturn, security.insecureAPI.getpw, security.insecureAPI.gets, security.insecureAPI.mkstemp, security.insecureAPI.mktemp, security.insecureAPI.rand, security.insecureAPI.vfork, unix.API, unix.Malloc, unix.MallocSizeof, unix.MismatchedDeallocator, unix.StdCLibraryFunctions, unix.Vfork, unix.cstring.BadSizeArg, unix.cstring.NullArg, valist.CopyToSelf, valist.Uninitialized, valist.Unterminated
    cppcheck: cppcheck-IOWithoutPositioning, cppcheck-StlMissingComparison, cppcheck-accessForwarded, cppcheck-accessMoved, cppcheck-argumentSize, cppcheck-arrayIndexOutOfBounds, cppcheck-arrayIndexOutOfBoundsCond, cppcheck-assertWithSideEffect, cppcheck-assignBoolToPointer, cppcheck-assignmentInAssert, cppcheck-autoVariables, cppcheck-autovarInvalidDeallocation, cppcheck-badBitmaskCheck, cppcheck-boostForeachError, cppcheck-bufferAccessOutOfBounds, cppcheck-charBitOp, cppcheck-charLiteralWithCharPtrCompare, cppcheck-checkCastIntToCharAndBack, cppcheck-clarifyStatement, cppcheck-compareBoolExpressionWithInt, cppcheck-comparePointers, cppcheck-comparisonFunctionIsAlwaysTrueOrFalse, cppcheck-comparisonOfBoolWithInvalidComparator, cppcheck-constStatement, cppcheck-containerOutOfBounds, cppcheck-copyCtorAndEqOperator, cppcheck-copyCtorPointerCopying, cppcheck-coutCerrMisusage, cppcheck-danglingLifetime, cppcheck-danglingReference, cppcheck-danglingTemporaryLifetime, cppcheck-deallocDealloc, cppcheck-deallocret, cppcheck-deallocuse, cppcheck-derefInvalidIterator, cppcheck-divideSizeof, cppcheck-doubleFree, cppcheck-duplInheritedMember, cppcheck-eraseDereference, cppcheck-exceptDeallocThrow, cppcheck-exceptThrowInDestructor, cppcheck-floatConversionOverflow, cppcheck-funcArgOrderDifferent, cppcheck-identicalConditionAfterEarlyExit, cppcheck-identicalInnerCondition, cppcheck-ignoredReturnValue, cppcheck-incompatibleFileOpen, cppcheck-incompleteArrayFill, cppcheck-incorrectCharBooleanError, cppcheck-incorrectLogicOperator, cppcheck-incorrectStringBooleanError, cppcheck-incorrectStringCompare, cppcheck-integerOverflow, cppcheck-invalidContainerLoop, cppcheck-invalidContainer, cppcheck-invalidFree, cppcheck-invalidFunctionArg, cppcheck-invalidFunctionArgBool, cppcheck-invalidFunctionArgStr, cppcheck-invalidIterator1, cppcheck-invalidLengthModifierError, cppcheck-invalidLifetime, cppcheck-invalidPrintfArgType_float, cppcheck-invalidPrintfArgType_n, cppcheck-invalidPrintfArgType_p, cppcheck-invalidPrintfArgType_s, cppcheck-invalidPrintfArgType_sint, cppcheck-invalidPrintfArgType_uint, cppcheck-invalidScanfArgType_float, cppcheck-invalidScanfArgType_int, cppcheck-invalidScanfArgType_s, cppcheck-invalidScanfFormatWidth, cppcheck-invalidScanfFormatWidth_smaller, cppcheck-invalidTestForOverflow, cppcheck-invalidscanf, cppcheck-iterators1, cppcheck-iterators2, cppcheck-iterators3, cppcheck-iteratorsCmp1, cppcheck-iteratorsCmp2, cppcheck-leakNoVarFunctionCall, cppcheck-leakReturnValNotUsed, cppcheck-leakUnsafeArgAlloc, cppcheck-literalWithCharPtrCompare, cppcheck-mallocOnClassError, cppcheck-mallocOnClassWarning, cppcheck-memleak, cppcheck-memleakOnRealloc, cppcheck-memsetClass, cppcheck-memsetClassFloat, cppcheck-memsetClassReference, cppcheck-memsetValueOutOfRange, cppcheck-memsetZeroBytes, cppcheck-mismatchAllocDealloc, cppcheck-mismatchSize, cppcheck-mismatchingContainerExpression, cppcheck-mismatchingContainers, cppcheck-missingMemberCopy, cppcheck-missingReturn, cppcheck-moduloAlwaysTrueFalse, cppcheck-multiplySizeof, cppcheck-negativeArraySize, cppcheck-negativeContainerIndex, cppcheck-negativeIndex, cppcheck-negativeMemoryAllocationSize, cppcheck-noCopyConstructor, cppcheck-noDestructor, cppcheck-noOperatorEq, cppcheck-nullPointer, cppcheck-nullPointerArithmetic, cppcheck-nullPointerArithmeticRedundantCheck, cppcheck-nullPointerDefaultArg, cppcheck-nullPointerRedundantCheck, cppcheck-objectIndex, cppcheck-operatorEqMissingReturnStatement, cppcheck-operatorEqToSelf, cppcheck-operatorEqVarError, cppcheck-oppositeInnerCondition, cppcheck-overlappingStrcmp, cppcheck-overlappingWriteFunction, cppcheck-overlappingWriteUnion, cppcheck-pointerAdditionResultNotNull, cppcheck-pointerArithBool, cppcheck-pointerSize, cppcheck-publicAllocationError, cppcheck-pureVirtualCall, cppcheck-raceAfterInterlockedDecrement, cppcheck-readWriteOnlyFile, cppcheck-redundantAssignInSwitch, cppcheck-redundantBitwiseOperationInSwitch, cppcheck-redundantCopyInSwitch, cppcheck-resourceLeak, cppcheck-rethrowNoCurrentException, cppcheck-returnAddressOfAutoVariable, cppcheck-returnAddressOfFunctionParameter, cppcheck-returnDanglingLifetime, cppcheck-returnLocalVariable, cppcheck-returnReference, cppcheck-returnTempReference, cppcheck-seekOnAppendedFile, cppcheck-selfAssignment, cppcheck-selfInitialization, cppcheck-shiftNegativeLHS, cppcheck-shiftNegative, cppcheck-shiftTooManyBits, cppcheck-shiftTooManyBitsSigned, cppcheck-signConversion, cppcheck-signedCharArrayIndex, cppcheck-sizeofCalculation, cppcheck-sizeofDivisionMemfunc, cppcheck-sizeofFunctionCall, cppcheck-sizeofsizeof, cppcheck-sizeofwithnumericparameter, cppcheck-sizeofwithsilentarraypointer, cppcheck-sprintfOverlappingData, cppcheck-staticStringCompare, cppcheck-stlBoundaries, cppcheck-stlIfFind, cppcheck-stlOutOfBounds, cppcheck-stlcstr, cppcheck-stlcstrReturn, cppcheck-stlcstrParam, cppcheck-stlcstrthrow, cppcheck-strPlusChar, cppcheck-stringCompare, cppcheck-stringLiteralWrite, cppcheck-suspiciousCase, cppcheck-suspiciousSemicolon, cppcheck-thisSubtraction, cppcheck-throwInNoexceptFunction, cppcheck-uninitDerivedMemberVar, cppcheck-uninitDerivedMemberVarPrivate, cppcheck-uninitMemberVar, cppcheck-uninitMemberVarPrivate, cppcheck-uninitStructMember, cppcheck-uninitdata, cppcheck-uninitstring, cppcheck-uninitvar, cppcheck-unknownEvaluationOrder, cppcheck-unsafeClassRefMember, cppcheck-unusedLabelSwitch, cppcheck-unusedLabelSwitchConfiguration, cppcheck-useClosedFile, cppcheck-uselessAssignmentPtrArg, cppcheck-uselessCallsCompare, cppcheck-uselessCallsEmpty, cppcheck-uselessCallsRemove, cppcheck-va_end_missing, cppcheck-va_list_usedBeforeStarted, cppcheck-va_start_referencePassed, cppcheck-va_start_subsequentCalls, cppcheck-va_start_wrongParameter, cppcheck-virtualCallInConstructor, cppcheck-virtualDestructor, cppcheck-writeReadOnlyFile, cppcheck-wrongPipeParameterSize, cppcheck-wrongPrintfScanfArgNum, cppcheck-wrongPrintfScanfParameterPositionError, cppcheck-wrongmathcall, cppcheck-zerodiv, cppcheck-zerodivcond
    [INFO 2024-02-01 11:11] - Starting static analysis ...
    [INFO 2024-02-01 11:11] - [1/3] cppcheck analyzed ub.c successfully.
    [INFO 2024-02-01 11:11] - [2/3] clangsa analyzed ub.c successfully.
    [INFO 2024-02-01 11:11] - [3/3] clang-tidy analyzed ub.c successfully.
    [INFO 2024-02-01 11:11] - ----==== Summary ====----
    [INFO 2024-02-01 11:11] - Successfully analyzed
    [INFO 2024-02-01 11:11] -   clang-tidy: 1
    [INFO 2024-02-01 11:11] -   clangsa: 1
    [INFO 2024-02-01 11:11] -   cppcheck: 1
    [INFO 2024-02-01 11:11] - Total analyzed compilation commands: 1
    [INFO 2024-02-01 11:11] - ----=================----
    [INFO 2024-02-01 11:11] - Analysis finished.
    [INFO 2024-02-01 11:11] - To view results in the terminal use the "CodeChecker parse" command.
    [INFO 2024-02-01 11:11] - To store results use the "CodeChecker store" command.
    [INFO 2024-02-01 11:11] - See --help and the user guide for further options about parsing and storing the reports.
    [INFO 2024-02-01 11:11] - ----=================----
    [INFO 2024-02-01 11:11] - Analysis length: 0.3319387435913086 sec.
    [WARNING 2024-02-01 11:11] - Analyzer 'gcc' is enabled but CodeChecker is failed to execute analysis with it: 'Incompatible version: GCC binary found is too old at v11.4.0; minimum version is 13.0.0. Maybe try setting an absolute path to a different analyzer binary via the env variable CC_ANALYZER_BIN?'. Please check your 'PATH' environment variable and the 'config/package_layout.json' file!
    Parsing input file '/tmp/reports/ub.c_clangsa_fb9868167746a12b0aa35cb54a22e877.plist'.
    [INFO 2024-02-01 11:11] - Html file was generated: /tmp/reports.html/ub.c_clangsa_fb9868167746a12b0aa35cb54a22e877.plist.html
    Parsing input file '/tmp/reports/ub.c_clang-tidy_fb9868167746a12b0aa35cb54a22e877.plist'.
    [INFO 2024-02-01 11:11] - Html file was generated: /tmp/reports.html/ub.c_clang-tidy_fb9868167746a12b0aa35cb54a22e877.plist.html
    Parsing input file '/tmp/reports/ub.c_cppcheck_0795e4a55ea44198516e5ae416d02dbb.plist'.
    [INFO 2024-02-01 11:11] - Html file was generated: /tmp/reports.html/ub.c_cppcheck_0795e4a55ea44198516e5ae416d02dbb.plist.html
    Parsing input file '/tmp/reports/ub.c_clangsa_0795e4a55ea44198516e5ae416d02dbb.plist'.
    [INFO 2024-02-01 11:11] - No report data in /tmp/reports/ub.c_clangsa_0795e4a55ea44198516e5ae416d02dbb.plist file.
    Parsing input file '/tmp/reports/ub.c_cppcheck_fb9868167746a12b0aa35cb54a22e877.plist'.
    [INFO 2024-02-01 11:11] - No report data in /tmp/reports/ub.c_cppcheck_fb9868167746a12b0aa35cb54a22e877.plist file.
    
    ----==== Severity Statistics ====----
    ----------------------------
    Severity | Number of reports
    ----------------------------
    HIGH     |                 2
    MEDIUM   |                 1
    ----------------------------
    ----=================----
    
    ----==== Checker Statistics ====----
    -------------------------------------------------------------
    Checker name                   | Severity | Number of reports
    -------------------------------------------------------------
    core.uninitialized.Assign      | HIGH     |                 1
    clang-diagnostic-uninitialized | MEDIUM   |                 1
    cppcheck-uninitvar             | HIGH     |                 1
    -------------------------------------------------------------
    ----=================----
    
    ----==== File Statistics ====----
    -----------------------------
    File name | Number of reports
    -----------------------------
    ub.c      |                 3
    -----------------------------
    ----=================----
    
    ----======== Summary ========----
    ---------------------------------------------
    Number of processed analyzer result files | 5
    Number of analyzer reports                | 3
    ---------------------------------------------
    ----=================----
    
    To view statistics in a browser run:
    > firefox /tmp/reports.html/statistics.html
    
    To view the results in a browser run:
    > firefox /tmp/reports.html/index.html



    ---------------------------------------------------------------------------

    CalledProcessError                        Traceback (most recent call last)

    Cell In [15], line 1
    ----> 1 get_ipython().run_cell_magic('bash', '', '# instrument a build first\nCodeChecker log -o /tmp/compile_commands.json --build "clang -o /tmp/ub /tmp/ub.c"\n# Then run the analyzer\nCodeChecker analyze /tmp/compile_commands.json -o /tmp/reports\nCodeChecker parse /tmp/reports -e html -o /tmp/reports.html\n\n# all in one\n#CodeChecker check --build "make" --output ./reports --clean \\\n#    --enable sensitive\n')


    File ~/.local/lib/python3.10/site-packages/IPython/core/interactiveshell.py:2362, in InteractiveShell.run_cell_magic(self, magic_name, line, cell)
       2360 with self.builtin_trap:
       2361     args = (magic_arg_s, cell)
    -> 2362     result = fn(*args, **kwargs)
       2363 return result


    File ~/.local/lib/python3.10/site-packages/IPython/core/magics/script.py:153, in ScriptMagics._make_script_magic.<locals>.named_script_magic(line, cell)
        151 else:
        152     line = script
    --> 153 return self.shebang(line, cell)


    File ~/.local/lib/python3.10/site-packages/IPython/core/magics/script.py:305, in ScriptMagics.shebang(self, line, cell)
        300 if args.raise_error and p.returncode != 0:
        301     # If we get here and p.returncode is still None, we must have
        302     # killed it but not yet seen its return code. We don't wait for it,
        303     # in case it's stuck in uninterruptible sleep. -9 = SIGKILL
        304     rc = p.returncode or -9
    --> 305     raise CalledProcessError(rc, cell)


    CalledProcessError: Command 'b'# instrument a build first\nCodeChecker log -o /tmp/compile_commands.json --build "clang -o /tmp/ub /tmp/ub.c"\n# Then run the analyzer\nCodeChecker analyze /tmp/compile_commands.json -o /tmp/reports\nCodeChecker parse /tmp/reports -e html -o /tmp/reports.html\n\n# all in one\n#CodeChecker check --build "make" --output ./reports --clean \\\n#    --enable sensitive\n'' returned non-zero exit status 2.

## Cppcheck

<https://cppcheck.sourceforge.io/>
<https://github.com/danmar/cppcheck>

```python
! cppcheck /tmp/ub.c
```

    [32mChecking /tmp/ub.c ...[0m
    [1m/tmp/ub.c:4:5: [31merror:[39m Uninitialized variable: x [uninitvar][0m
        x++;
        ^

```python

```

```python
%%file /tmp/blast.sh
CCOPTIONS = -Wall -Wpedantic -fanalzye -fsanitize=address,bounds,undefined
clang $CCOPTIONS $1 -o  /tmp.a.out && ./a.out 
gcc $CCOPTIONS $1 &&
#cppcheck --enable=all $1
valgrind --leak-check=full --show-leak-kinds=all ./a.out
# codechecker
# infer


```

<https://github.com/verateam/vera> Probably old
clang-tidy also runs analyzer? clang-tidy-diff.py

```bash
%%bash
apt install opam
opam init -y
eval $(opam env)
git clone https://github.com/rems-project/cerberus.git
cd cerberus
opam install --deps-only ./cerberus-lib.opam ./cerberus.opam
make
```

```bash
%%bash
cd ~/Downloads/cerberus
opam install angstrom
make cerberus-bmc
# make all

```

    [NOTE] Package angstrom is already installed (current version is 0.15.0).


    [DUNE] cerberus-bmc


    File "backend/bmc/bmc_utils.ml", lines 326-356, characters 2-3:
    326 | ..(match pe_ with
    327 |   | PEsym s -> PEsym s
    328 |   | PEimpl impl1 -> PEimpl impl1
    329 |   | PEval v -> PEval v
    330 |   | PEconstrained cs ->
    ...
    353 |   | PEis_unsigned pe -> PEis_unsigned (self( 1) pe)
    354 |   | PEbmc_assume pe -> PEbmc_assume (self( 1) pe)
    355 |   | PEare_compatible( pe1, pe2) -> PEare_compatible( (self( 1) pe1), (self( 2) pe2))
    356 |   )..
    Error (warning 8 [partial-match]): this pattern-matching is not exhaustive.
    Here is an example of a case that is not matched:
    (PEconv_int (_, _)|PEwrapI (_, _, _, _)|
    PEcatch_exceptional_condition (_, _, _, _))
    make: *** [Makefile:69: cerberus-bmc] Error 1



    ---------------------------------------------------------------------------

    CalledProcessError                        Traceback (most recent call last)

    Cell In [3], line 1
    ----> 1 get_ipython().run_cell_magic('bash', '', 'cd ~/Downloads/cerberus\nopam install angstrom\nmake cerberus-bmc\n')


    File ~/.local/lib/python3.10/site-packages/IPython/core/interactiveshell.py:2362, in InteractiveShell.run_cell_magic(self, magic_name, line, cell)
       2360 with self.builtin_trap:
       2361     args = (magic_arg_s, cell)
    -> 2362     result = fn(*args, **kwargs)
       2363 return result


    File ~/.local/lib/python3.10/site-packages/IPython/core/magics/script.py:153, in ScriptMagics._make_script_magic.<locals>.named_script_magic(line, cell)
        151 else:
        152     line = script
    --> 153 return self.shebang(line, cell)


    File ~/.local/lib/python3.10/site-packages/IPython/core/magics/script.py:305, in ScriptMagics.shebang(self, line, cell)
        300 if args.raise_error and p.returncode != 0:
        301     # If we get here and p.returncode is still None, we must have
        302     # killed it but not yet seen its return code. We don't wait for it,
        303     # in case it's stuck in uninterruptible sleep. -9 = SIGKILL
        304     rc = p.returncode or -9
    --> 305     raise CalledProcessError(rc, cell)


    CalledProcessError: Command 'b'cd ~/Downloads/cerberus\nopam install angstrom\nmake cerberus-bmc\n'' returned non-zero exit status 2.

```bash
%%bash
cd ~/Downloads/cerberus
dune exec cerberus -- --help

```

    CERBERUS(1)                     Cerberus Manual                    CERBERUS(1)
    
    
    
    NAME
           cerberus - Cerberus C semantics
    
    SYNOPSIS
           cerberus [OPTION]… [FILE]…
    
    ARGUMENTS
           FILE
               source C or Core file
    
    OPTIONS
           --agnostic
               Asks Cerberus to delay looking at implementation settings until as
               late as possible. This makes the pipeline somewhat implementation
               agnostic.
    
           --args="ARG1 ARG2 ..."
               List of arguments for the C program
    
           --ast=LANG1,...
               Pretty print the intermediate syntax tree for the listed languages
               (ranging over {cabs, ail, core}).
    
           --batch
               makes the execution driver produce batch friendly output
    
           -c  Run frontend generating a target '.co' core object file.
    
           --charon-batch
               makes the execution driver produce batch friendly output (for
               Charon)
    
           --concurrency
               Activate the C11 concurrency
    
           --cpp=CMD (absent=cc -std=c11 -E -CC -Werror
           -Wno-builtin-macro-redefined -nostdinc -undef -D__cerb__)
               Command to call for the C preprocessing.
    
           -D NAME[=VALUE], --define-macro=NAME[=VALUE]
               Adds an implicit #define into the predefines buffer which is read
               before the source file is preprocessed.
    
           -d N, --debug=N (absent=0)
               Set the debug message level to N (should range over [0-9]).
    
           --defacto
               relax some of the ISO constraints (outside of the memory)
    
           --dignore-bitfields
               (DEBUG) accept and ignore bit-field width specifiers. CAUTION: the
               constraints relating to bit-fields are NOT checked, and the
               desugaring produces Ail struct/union types with normal members.
               This flag will be removed when support for bit-fields is added.
    
           -E  Run only the preprocessor stage.
    
           --exec
               Execute the Core program after the elaboration.
    
           --fs=DIR
               Initialise the internal file system with the contents of the
               directory DIR
    
           --fs-dump
               dump the file system at the end of the execution
    
           -I DIR, --include-directory=DIR
               Add the specified directory to the search path for theC
               preprocessor.
    
           --impl=NAME (absent=gcc_4.9.0_x86_64-apple-darwin10.8.0)
               Set the C implementation file (to be found in
               CERB_COREPATH/implsand excluding the .impl suffix).
    
           --include=VAL
               Adds an implicit #include into the predefines buffer which is read
               before the source file is preprocessed.
    
           --iso
               sets the switches corresponding to the ISO semantics (this
               overrides --switches if it is also present)
    
           --json-batch
               outputs the executions in json
    
           -l X
               This option tells the core linker to search for libX.co in the
               library search path.
    
           -L X
               Adds a new library search path.
    
           --mode=MODE (absent=random)
               Set the Core evaluation mode (interactive | exhaustive | random).
    
           --nolibc
               Do not search the standard system directories for include files.
    
           --nostdinc
               Do not search includes in the standard lib C directories.
    
           -o VAL
               Write output to file.
    
           --permissive
               allow extensions to ISO (by default Cerberus behaves like compilers
               with -pedantic)
    
           --pp=LANG1,...
               Pretty print the intermediate programs for the listed languages
               (ranging over {ail, core}).
    
           --pp_ail_out=VAL
               Write Ail pprint to a file.
    
           --pp_core_out=VAL
               Write Core pprint to a file.
    
           --pp_flags=VAL
               Pretty print flags [annot: include location and ISO annotations,
               loc: include C source locations].
    
           --progress
               Progress mode: the return code indicate how far the source program
               went through the pipeline [1 = total failure, 10 = parsed, 11 =
               desugared, 12 = typed, 13 = elaborated, 14 = executed]
    
           -r DIR, --runtime=DIR
               custom Cerberus runtime directory
    
           --rewrite
               Activate the Core to Core transformations
    
           --sequentialise
               Replace all unseq() with left to right wseq(s)
    
           --switches=SWITCH1,...
               list of semantics switches to turn on (see documentation for the
               list)
    
           --syntax-only
               Stop the pipeline after the Ail typechecking (only supported when
               called on .c files)
    
           --trace
               trace memory actions
    
           --typecheck-core
               typecheck the elaborated Core program
    
           -U VAL
               Adds an implicit #undef into the predefines buffer which is read
               before the source file is preprocessed.
    
    COMMON OPTIONS
           --help[=FMT] (default=auto)
               Show this help in format FMT. The value FMT must be one of auto,
               pager, groff or plain. With auto, the format is pager or plain
               whenever the TERM env var is dumb or undefined.
    
           --version
               Show version information.
    
    EXIT STATUS
           cerberus exits with:
    
           0   on success.
    
           123 on indiscriminate errors reported on standard error.
    
           124 on command line parsing errors.
    
           125 on unexpected internal errors (bugs).
    
    
    
    Cerberus git-4806a4479                                             CERBERUS(1)

```python
%%file 
struct S {
  int i;
  char c;
} s;

int main(void) {
  return sizeof(*(&s));
}
```

```python
%%file
int main(void) {
  char a = 0;
  short int b = 0;
  return sizeof(b) == sizeof(a+b);
}
```

```python
int main(void) {
  char a = ' ' * 13;
  return a;
}
 
```

```python
int main(void) {
  int i = 16;
  return (((((i >= i) << i) >> i) <= i));
}
```

```python
int main(void) {
  int i = 0;
  return i++ + ++i;
}
```
