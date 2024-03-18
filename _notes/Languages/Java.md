---
layout: post
title: Java
---
- [Java](#java)
  - [java runtime](#java-runtime)
  - [javac](#javac)
  - [jar](#jar)
  - [build](#build)
  - [Bytecode](#bytecode)
- [Kotlin](#kotlin)
- [Scala](#scala)

# Java

java has intersection types? <https://en.wikipedia.org/wiki/Intersection_type>

<https://docs.oracle.com/en/java/javase/21/>
java 21 has some pretty cool stuff <https://docs.oracle.com/en/java/javase/21/language/index.html#Java-Platform%2C-Standard-Edition>
raw function execution <https://docs.oracle.com/en/java/javase/21/language/unnamed-classes-and-instance-main-methods.html>
record  <https://docs.oracle.com/en/java/javase/21/language/records.html>
patterns <https://docs.oracle.com/en/java/javase/21/language/pattern-matching.html>
switch expressions
<https://docs.oracle.com/en/java/javase/21/language/string-templates.html> template strings

```java
// cd "/tmp/" && javac --enable-preview --source 21 tempyjltsrm.java && java --enable-preview tempyjltsrm
// java --enable-preview --source 21 myfile.java
record Term(String head, Term[] args) {}

// naked main "anonymous classes"
void main() {
    var t  = new Term("foo", new Term[0]); // local variable inference
    System.out.println(STR."\{t}"); // string interpolation
    switch(t) { // pattern matching
        case Term(var h, var args) -> System.out.println(h);
        default -> System.out.println("match fail");
    }
}

```

```java

//static record Foo() {}
import java.util.ArrayList;
class Main{  
    public static void main(String args[]){  
     System.out.println("Hello Java");  
    }  
}  

```

<https://github.com/akullpp/awesome-java>

java decompilation

java webassembly teavm cheerpj

idea intellij

## java runtime

`java -jar Main.jar`
The directory structure matters.
The names of classes need to match

classpath is where java looks for stuff
`-agentlib:libname[=options]` is native libraries

## javac

## jar

jars are like zip files of packages in a single file

## build

maven
gradle

## Bytecode

The java VM
verify?

# Kotlin

```kotlin

fun main(){
    println("hello world")
}

```

# Scala

```scala
// hello world

```
