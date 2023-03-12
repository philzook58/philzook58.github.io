---
date: 2023-03-11
layout: post
title: "MiniLitelog: Easy Breezy SQLite datalog"
description: Simple Shallow Embedding of Seminaive Datalog into SQLite
tags: datalog sqlite
---

- [Datalog Transformations](#datalog-transformations)
  - [Transitivity Query](#transitivity-query)
  - [Step 1: Linearize the Pattern Variables](#step-1-linearize-the-pattern-variables)
  - [Step 2: Structifying](#step-2-structifying)
- [It's SQL time](#its-sql-time)
  - [Naive SQL translation](#naive-sql-translation)
  - [Embedding Naive Evaluation in SQLite Python](#embedding-naive-evaluation-in-sqlite-python)
  - [Simple Seminaive](#simple-seminaive)
    - [Seminaive with timestamps](#seminaive-with-timestamps)
- [Bits and Bobbles](#bits-and-bobbles)


There's just _something_ about datalog.

If you want to know what you can do with datalog, I've got a [pile of stuff here](https://www.philipzucker.com/notes/Languages/datalog/)

This blog post about is about a very lightweight encoding of datalog to SQLite. SQLite bindings exist in nearly every language so this light embedding makes it very easy to make a pretty decent datalog in any language of your choice.

I've previously explored using stock SQL engines to power a datalog in these posts:

- [Snakelog: A Python DSL for Datalogs](https://www.philipzucker.com/snakelog-post/)
- [Datalite: A Simple Datalog Built Around SQLite in Python](https://www.philipzucker.com/datalite/)
- [Duckegg: A Datalog / Egraph Implementation Built Around DuckDB](https://www.philipzucker.com/duckegg-post/)

But I think this is the cleanest simplest encoding yet. Part of the trick is a strategic retreat on the definition of datalog

There are the impedance mismatches between SQL and datalog. These are crucial:
- Recursion or Fixpoint support. This is part of the point of datalog. SQL has a feature [recursive common table expressons](https://www.sqlite.org/lang_with.html#recursive_common_table_expressions) which is clunky and limited. An important part of supporting the fixpoint is supporting the seminaive optimization, where highly redundant work is not done.
- Set vs Bag (multiset) semantics. As noted in previous posts, the clean way to fix this in SQLite is to declare a table with all columns as primary keys `CREATE TABLE edge(x,y, PRIMARY KEY (x,y));` and use `INSERT INTO OR IGNORE`

These differences are less crucial:
- Nonlinear vs Linear patterns. Datalog allows us to bind variables twice as an implicit equality constraint
- Named vs Unnamed style (See [section 3.2](http://webdam.inria.fr/Alice/pdfs/Chapter-3.pdf) of the [Alice](http://webdam.inria.fr/Alice/) book). SQL allows you to attach names to _rows_ (`FROM mytable AS myrow`) and refers to columns by label (`myrow.foo`). Datalog conventionally binds names to entries (`mytable(foo_entry,bar_entry)`) (a data item in a column of a particular row) and refers to columns by position (columns 1, 2, 3, 4, etc).

# Datalog Transformations
So let's first take a datalog program and show how to rewrite it  to strip out the less crucial differences such that it is easier to translate to SQL.

## Transitivity Query

To talk concretely, here is the (yawn. I kid. I love it.) transitive closure program for [souffle datalog](https://souffle-lang.github.io/) expressing reachability in a graph. 

```souffle
.decl edge(a : number, b : number)
.decl path(a : number, b : number)
edge(1,2). edge(2,3). edge(3,4).
path(x,y) :- edge(x,y).
path(x,z) :- edge(x,y), path(y,z).
.output path(IO=stdout)

/* Output:
---------------
path
a       b
===============
1       2
1       3
1       4
2       3
2       4
3       4
===============
*/
```

## Step 1: Linearize the Pattern Variables
A useful datalog normal form is to make sure every variable is bound only once and use explicit `=` to create constraints instead. Let's call this linear normal form.

In the above, `path(x,z) :- edge(x,y), path(y,z).` becomes `path(x,z) :- edge(x,y), path(y1,z), y = y1.`

This transformation is useful because many languages do not offer nonlinear patterns. For example, this transformation is needed in the for loop interpretation of rules.

```python
for (x,y) in edge:
    for (y1,z) in path:
        if y == y1:
            yield (x,z)
```

Or alternatively in the cute generator form which really syntactically looks like a rule

```python
edge = {(1,2), (2,3)}
path = set()
for i in range(10):
    path |= {(x,y) for x,y in edge} # path(x,y) :- edge(x,y).
    path |= {(x,z) for x,y in edge for y1, z in path if y == y1} #path(y,z) :- edge(x,y), path(y,z).
```

If we used the variable `y` twice, we shadow it instead of filter on it. This is not what is intended.

```python
#BAD
for (x,y) in edge:
    for (y,z) in path:
        yield (x,z)
```

## Step 2: Structifying

Now that we've normalized, the next transformation is to replace binding entries with instead binding rows.

We can show this struct convention in souffle. We make a type to encode the full row and now we bind variables `edge0` and `path0` to this full row struct and extract its fields.

```souffle
.type row = [a : number, b : number]

.decl edge(r : row)
.decl path(r : row)
edge([1,2]). edge([2,3]). edge([3,4]).
path(r) :- edge(r).
path([x,z]) :- edge(edge0), path(path0), edge0 = [x,y], path0 = [y1,z], y = y1.
.output path(stdout=IO)
```

This is a very bad thing to do in souffle, because it completely subverts souffle's indexing mechanisms. There is not conceptual issue however. Souffle so happens to not have field accessor notation, but does have structural pattern matching. This is not fundamental.

# It's SQL time
Ok, so judo move 1: just write your datalog program in the above form in the first place.

"Standard" Datalog is not god given really. The point we are at is a perfectly reasonable (interesting even) struct-centric, column-named, linear patterned datalog.

If you really insist on the features of standard datalog, you can add them one by one. I have shown how to do so in previous blog posts.

This SQLlog isn't _that_ much worse than regular datalog and the compilation burden of doing these translations is not worth it unless you're writing a lot of datalog or wiling to maintain a significant library. 

And now it is easy to translate to SQL mechanically as a lightweight design pattern or library.
We retain the essential points of set semantics, fixpoint calculation, and the seminaive optimization.

## Naive SQL translation

It is simple to translate a single application of a rule to a SQL statement.

- The head of a rule `path(edge0.a,path0.b)` becomes `INSERT OR IGNORE INTO path SELECT edge0.a, path0.b`
- The body of the rule gets split into a binding part and a filtering part. `path(path0), edge(edge0)` becomes `FROM path AS path0, edge AS edge0` and `edge0.b = path0.a` goes into the `WHERE clause.

The SQLite [UPSERT semantics](https://www.sqlite.org/lang_UPSERT.html) give us the set semantics of datalog without explicit deduplication queries. We enable it by defining tables with every column as a primary key `CREATE TABLE edge(a INTEGER, b INTEGER, PRIMARY KEY (a,b));` and by using `INSERT OR IGNORE INTO` which will not inert new tuples if they violate the primary key constraint.

```sql
CREATE TABLE edge(a INTEGER, b INTEGER, PRIMARY KEY (a,b)); -- .decl edge(x : number, y : number)
CREATE TABLE path(a INTEGER, b INTEGER, PRIMARY KEY (a,b)); -- .decl path(x : number, y : number)

INSERT OR IGNORE INTO edge(a,b)
VALUES (1,2),(2,3),(3,4); -- edge(1,2). edge(2,3). edge(3,4).

-- path(X,Y) :- edge(X,Y).
INSERT OR IGNORE INTO path SELECT DISTINCT edge0.a, edge0.b   -- the head of the rule gives the insert and select fields  
FROM edge as edge0; -- The body of the rule gives FROM and WHERE  

-- path(x,z) :- edge(x,y), path(y,z).
INSERT OR IGNORE INTO path SELECT DISTINCT edge0.a, path0.b   -- the head of the rule gives the insert and select fields  
FROM edge as edge0, path as path0
WHERE edge0.b = path0.a; -- The body of the rule gives FROM and WHERE  
```

## Embedding Naive Evaluation in SQLite Python

In order to actually compute the fixpoint, we need to repeatedly apply these queries. It is useful to do this in a programming language. Python is not essential, but it is familiar and convenient. [SQLite](https://docs.python.org/3/library/sqlite3.html) ships in the standard library of python for example. The same thing can easily be done in the language of your choosing.

Basically the complicated looking format strings are just constructing the SQL queries above for you.

```python
import sqlite3

class Rule():
  def __init__(self, head : str, selects, froms , where="TRUE"):
    from_str = ", ".join(f"{table} AS {row}" for table,row in froms)
    self.sql = f"""
    INSERT OR IGNORE INTO {head} SELECT DISTINCT {selects}  -- head
    FROM {from_str}  -- body
    WHERE ({where})  -- body
    """
  def execute(self,cur):
    cur.execute(self.sql)  

def create_rel(cur, name, *fields):
  fields = ", ".join(fields)
  sql = f"CREATE TABLE {name}({fields}, PRIMARY KEY ({fields}))" # set semantics
  cur.execute(sql)

con = sqlite3.connect(":memory:") # in memory database. Faster maybe?
cur = con.cursor()
create_rel(cur, "edge", "a", "b")
create_rel(cur, "path", "a", "b")

base = Rule("path", "edge0.a, edge0.b",
                     [("edge", "edge0")])
trans = Rule("path", "edge0.a, path0.b",
                     [("path", "path0"), ("edge", "edge0")],
                     where="edge0.b = path0.a")

ruleset = [base, trans]
cur.executemany("insert into edge values (?, ?)", [(1,2), (2,3), (3,4)])
# The "fixpoint"
# punt on actually performing fixpoint until the next section
for i in range(10):
    for rule in ruleset:
        rule.execute(cur)
print("path", cur.execute("select * from path").fetchall())
print("edge", cur.execute("select * from edge").fetchall())
```

## Simple Seminaive

The essential idea of seminaive iteration is that in order to derive something new, a rule must select at least one new tuple to work on. Typically, you do this by maintaining a delta per relation of changes since the last iteration. One iteration is one application of all the rules.

One way of organizing an embedded datalog is to make a master database object that remembers all the bits of metadata you may need, like delta relations, rules, and such and organizes each iteration.

However, a nice way of separating concerns is to make rule objects that maintain their own timestamp state. Now rules do not need to know about the existence of other rules, nor of any relation they do not touch.


### Seminaive with timestamps
I was discussing wth Langston Barrett their sqlite/duckdb based datalog and they mentioned that they were using timestamps.

It has come up before that there is a generalization of seminaive where you don't need to structure your execution into iterations can be done if you maintain timestamps. The timestamps are stored per rule. You can filter the rule's query such that there must be at least one tuple since the last timestamp it was executed. Now you can run the rules in any order you want and maintain correctness.

While the most familiar timestamps we may be familiar with are a unix time, or an iteration number, timestamps with more structure are really interesting and useful. A [vector timestamp](https://en.wikipedia.org/wiki/Vector_clock) of the sqlite database can be made that is a tuple of the maximum rowids of every table. In principle this timestamps is not totally ordered, but because sqlite is sequentialized, no incomparable timestamps will ever be produced. As an aside, it is interesting to consider what might happen or how to deal if this is nt the case.

SQLite has a very cute feature of [rowids](https://www.sqlite.org/lang_createtable.html#rowid). Every table has an implicit unique id unless you explicitly turn this feature off. And in fact these ids monotonically increase. By using this feature rather than adding a custom timestamp field, the impedance mismatch between the SQL and datalog worlds is reduced.

Typically seminaive is treated by splitting each rule into many rules, with a different instance of a relation replaced with it's delta version in each. However, using rowids, we can place the constraint of having one new tuple instead in the `WHERE` clause

```sql
WHERE (row1.rowid > timestamp1 OR row2.rowid > timestamp2 OR row3.rowid > timestamp3 ...)
```

And here is an extension of the above python to record and filter on the timestamps. The rule object maintains the most recent timestamp upon which the rule was run.

```python


class Rule():
  def __init__(self, head : str, selects, froms , where="TRUE"):
    from_str = ", ".join(f"{table} AS {row}" for table,row in froms)
    seminaive_filter_str = " OR ".join( f"{row}.rowid > ?" for _,row in froms ) 
    self.sql = f"""
    INSERT OR IGNORE INTO {head} SELECT DISTINCT {selects}  -- head
    FROM {from_str}  -- body
    WHERE ({where})  -- body
    AND ({seminaive_filter_str})  -- seminaive
    """

    self.timestamp = tuple(-1 for _ in froms)
    select_str = ", ".join(f"MAX({row}.rowid)" for _,row in froms)
    self.ts_query = f""" 
    SELECT {select_str} FROM {from_str} 
    """

  def execute(self,cur):
    ts = self.timestamp # the last time this rule was run
    self.timestamp = cur.execute(self.ts_query).fetchone() # update timestamp
    cur.execute(self.sql, ts) 

def fixpoint(cur, ruleset):
  done = False
  while not done:
    done = True
    for rule in ruleset:
      old_ts = rule.timestamp 
      rule.execute(cur)
      done &= old_ts == rule.timestamp
    
def create_rel(cur, name, *fields):
  fields = ", ".join(fields)
  sql = f"CREATE TABLE {name}({fields}, PRIMARY KEY ({fields}))" # set semantics
  cur.execute(sql)

import sqlite3
con = sqlite3.connect(":memory:")
cur = con.cursor()
create_rel(cur,"edge", "a", "b")
create_rel(cur,"path", "a", "b")

base = Rule("path", "edge0.a, edge0.b",
                     [("edge", "edge0")])
trans = Rule("path", "edge0.a, path0.b",
                     [("path", "path0"), ("edge", "edge0")],
                     where="edge0.b = path0.a")
ruleset = [base, trans]
cur.executemany("INSERT INTO edge VALUES (?, ?)", [(1,2), (2,3), (3,4)]) # initialize
fixpoint(cur,ruleset)

print("path", cur.execute("SELECT * FROM path").fetchall())
print("edge", cur.execute("SELECT * FROM edge").fetchall())
```

# Bits and Bobbles

In addition, if we track the timestamps of the head before and after rule application and record them in a list, we get a lightweight provenance mechanism for free. This timestamp list get an explicit representation of which ranges of tuple were derived by this rule application (those with `rowid` between the timestamps occurring before and after the rule application) and when. When the time comes to figure out how a partcular tuple was derived, these breadcrumbs are enough to make the reconstruction search-free.

Stratification of rulesets. You can avoid some unnecessary work... Wait... Is there even a point to this? The timestamps means that probably running a rule is negligible. Well, that was true in regular seminaive too. Hmm.

Is running datalog on postgres interesting? The chase on postgres?

Model checking using SQL.

Another database trick I love is Tombstones. Is there a list of stuff like timestamps and tombstones somewhere?

Constraint Handling rules

C datalog. I was trying to reduce the compilation burden from datalog to SQL. 

Compositional Sql statements with `type semantics = select * from * where`

Swapping in duckdb. Duckdb recently gained upsert semantics <https://duckdb.org/docs/sql/statements/insert>
 <https://github.com/duckdb/duckdb/issues/61> .

Langston pointed out:
- Dynamism in the ability of sqlite to make it's query plan at runtime is one reason to be hopeful





One really wants to reuse the engineering and ecosystem behind mature SQL engines but also clean and predictable interoperation of the Datalog world with SQL is really useful. Part of the point of this exercise is that sometimes one wants to break out of the rigid conventions of datalog to do something bespoke and interesting. SQL gives you a lot of less principled but powerful imperative control over the database.

It s desirable for the translation to SQL tables to not be confusing and weird. If I need to store extra metadata in the relations, then it can't run over ordinary SQLite tables. They must be special tables and the abstraction is broken or I need a significant translation api between my datalog world and the regular SQL world.

I also want to full power of SQL available in the rules. This include for example interesting side conditions and subqueries, and built in functions. I tried to do this in the previous iteration
In previous iterations

I also get very frustrated by deep embeddings. There is just so much bulk junk that mostly is unnecessary when you build and AST and interpret it away. A shallow embedding is lots of fun. You get to make fun little combinators and in future use one isn't locked away.

The whole _point_ of programming languages is what shallow embeddings they make possible. Everything is deep embeddeable in everything (turing complete). What is shallow is very different between languages. Different tools for different jobs.

We can either write a compiler to convert from regular datalog to spartan datalog or just write our programs in the spartan datalog to begin with. I'm a little inclined to the latter. It's not that bad.
The judo trick is to change what I mean by datalog.
The essential point of datalog is the iterated fixpoint.

I did things the heavy handed obvious way. It isn't that hard to do the appropriate unifications and carry the various compile time maps that connect datalog entities to SQL entities, and generate fresh symbols all over the place, but it was annoying and a little hacky and untrustworthy. It may be still worth doing as I think the niceties datalog offers are worth it if you're going beyond just a handful of rules.

Arguably the above python is less clear than just writing out the SQL. But the subtle move is making `Rule` an object. Now the rule can track state. This is important when we go to treat seminaive.

Demonstrating the point of language independence, here is the same thing in ocaml.

```ocaml
#use "topfind";;
#require "sqlite3";;

let rule head select froms where = 
    let ts = ref (List.map (fun _ -> -1) body) in
    let sql = 
    fun cur ->
        let old_ts = !ts in
        Sqlite3.exec db sql
        ts := 
let create_rel name cols db = 
    Sqlite3.exec db "CREATE TABLE " ^ name ^ "()"

let () =
    let open Sqlite3 in
    let& db = Sqlite3.db_open ~memory:true ":memory:" in
    let () = Sqlite3.exec db "CREATE TABLE edge(a,b, PRIMARY KEY (a,b))" in
    let () = Sqlite3.exec db "CREATE TABLE path(a,b, PRIMARY KEY (a,b))" in


```