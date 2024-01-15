

```C
// singleton using static?
typedef enum msg {INC, DEC, GET} msg;
int mycounter(msg msg){
    static int x = 0;
    switch(msg){
        case INC:
            x++;
            break;
        case DEC:
            x--;
            break;
        case GET:
            return x;
    }
}

int main(){
    mycounter(INC);
    mycounter(INC);
    mycounter(INC);
    mycounter(DEC);
    int x = mycounter(GET);
    printf("%d", x);
}


```


https://en.wikipedia.org/wiki/Object-oriented_programming


SmallTalk

Gang of 4

Visitor pattern

Message passing

Actor model

Codata, coalgebra

subtyping
contravariant
covariant

pub/sub

late binding

records of functions

open recursion - this, self

encapsulation

http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.158.6803&rep=rep1&type=pdf objects as sheaves

GUIs, automata, controllers, 

cardelli & abadi - theory of objects


# Aspect Oriented
Not sure this is persay realted to object oriented. But it feels similar
- join points
- pointcuts - a setof join points https://en.wikipedia.org/wiki/Pointcut
aspects

Weaving is the process of taking aspects and code and combining them

Some are source to source


Realted to metaobject protocols. A weakening?


ASP is structured comefrom?

[15-819 Objects and Aspects: Language Support for Extensible and Evolvable Software](https://www.cs.cmu.edu/~aldrich/courses/819/) Cool literature. Krishnaswami? Maybe he was a grad student 

[An overview of aspectJ](https://www.cs.ubc.ca/~gregor/papers/kiczales-ECOOP2001-AspectJ.pdf)
# interface
https://en.wikipedia.org/wiki/Interface_(object-oriented_programming)
# Multiple inheritance
# Mix-ins
https://en.wikipedia.org/wiki/Mixin
You get the pieces of a class without being an inheritor of that class. Ok.

# Traits
Related to mixins but not applied linearly?
https://en.wikipedia.org/wiki/Trait_(computer_programming)

# Multimethods
[Object-Oriented Multi-Methods in Cecil](https://www.cs.cmu.edu/~aldrich/courses/819/cecil-oo-mm.pdf)
The CLOS

# Metaobject protocols


# Prototypes
[Self the power of simplicity](https://www.cs.cmu.edu/~aldrich/courses/819/self.pdf)