---
layout: post
title: Javascript
---

{% include_relative javascript/test.html %}

<https://pnpm.io/>
npm
yarn

yo

grunt
gulp

typescript
<https://www.typescriptlang.org/docs/handbook/tsconfig-json.html>

webpack

eslint

react

vs code extension
activation points
contributes

using - like python with

```javascript
console.log("hello")
tokens = [
    ["LPAREN", `\\)`],
    ["RPAREN", `\\(`],
    ["NUMBER", `\\d+`],
    ["PLUS", `\\+`],
    ["MINUS", `\\-`],
    ["TIMES", `\\*`],
    ["DIVIDE", `\\/`],
    ["WS", `\\s+`],

]
const re = RegExp(tokens.map(([name, pattern]) => `(?<${name}>${pattern})`).join("|"), "g")
console.log(re)
console.log("123 foo bar ()".matchAll(re))
for(x in "123 foo bar ()".matchAll(re)) {
    console.log(x)
}

```

```typescript
console.log("hello")
```
