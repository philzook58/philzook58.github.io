<https://chat.openai.com/share/1bf6bb1a-e224-4d53-a748-b2291994fbe6>

Building an interactive proof kernel is one of those things that mayb you don't realize you can do. Like an operating system or a browser, it's just another kind of program.

Most resources out there describe how to do this in a functional language (OCaml, Haskell, etc), but I think it's useful to do it in a language like python. The extra impedance mismatch of bumbling through a language that is unfamiliar and a topic that is also unfamiliar can be too intimidating.

The basic approach of many proof systems is to try and build a small trusted kernel through which all your steps pass through. Then a much larger body of untrusted helper functionality can exist around this without compromising the integrity of the system.

Properties/features of the underlying language can help achieve this separation of concerns. In the LCF approach, the mechanism of abstract types is used to control valid proofs. `Theorem` is an abstract type, probably basically a wrapper around a formula abstract syntax tree. Just like how you can't screw with the internals of some dictiontary data structure, you can't screw around with the inside of `Theorem`. You can however request a copy of the information inside to play around with.

Python is a pretty uncontrolled language. It is hard to _really really_ enforce any kind of discipline because there is mutability and introspection everywhere. This distinction is however a matter of degree. Every language has some kind of escape hatch. OCaml has `Obj.magic` and Haskell has `unsafeCoerce`. The point is to protect you from accidental unsoundness, not antagonistic attacks. That requires a different design.

John Harrison's Handbook of Practical Logic and Automated Reasoning has some excellent examples.

# Hidden Constructor

```python
from dataclasses import dataclass

Formula = str
Formula = set[set[int]] #cnf
Proof = list[str]

@dataclass(frozen=True)
class Theorem():
    formula: Formula
    proof: Proof

def resolve(t1,t2, i):
    assert i in t1
    assert -i in t2
    return Theorem(t1.union(t2))
```

# Central Authority

# Crypto Signing

```python
import hashlib


SECRET = "no_underwear"
def validate(th):
    hsh = th[0]
    formula = th[1]
    return hash(self.SECRET, formula) == hsh
def modus(self, th1, th2): # A => B and A gives B
    if not validate(th1) or not validate(th2):
        return None
    match th1[1], th2[1]:
        case ("=>", A,  B), A1:
            if A == A1:
                return (hash(self.SECRET, B), B)

# server receivers a theorem and checks it's validity
from flask import Flask, request, jsonify

app = Flask(__name__)
@app.route('/modus', methods=['POST'])
def modus_api():
    received_object = request.json
    return jsonify(modus(request.A, request.B))

if __name__ == "__main__":
    app.run(debug=True, port=9999)

```

```python
import requests

def send_object_to_server(obj):
    response = requests.post("http://127.0.0.1:9999/send", json=obj)
    return response.json()


def proof_script():
    
obj_to_send = {"hello": "world"}
response = send_object_to_server(obj_to_send)
print("Received response:", response)

```

# Proof Objects

We so far have counted on trustability in the process. We can also just record a trace of the proof process (the sequence of calls with what parameters). We can then check this trace if we record it at a later time.

It is this method where the famed Curry Howard correspondence comes into play. These traces/proof trees can be naturally represented as lambda calculus terms for some logics.
