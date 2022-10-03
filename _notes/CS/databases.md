---
layout: post
title: Databases
---

- [Key Value Store](#key-value-store)
- [Algorithms](#algorithms)
- [Theory](#theory)
  - [Conjunctive Queries](#conjunctive-queries)
  - [Schema](#schema)
  - [Functional Dependencies](#functional-dependencies)
  - [Query Optimization](#query-optimization)
  - [The Chase](#the-chase)
- [SQL](#sql)
  - [indices](#indices)
  - [views](#views)
  - [triggers](#triggers)
  - [Aggregate functions](#aggregate-functions)
  - [Window Functions](#window-functions)
- [Ontology Formats](#ontology-formats)
- [Optimal Joins](#optimal-joins)
- [Vectorized Execution](#vectorized-execution)
- [Multi Version Concurrency Control](#multi-version-concurrency-control)
- [Duckdb](#duckdb)
- [Relational AI](#relational-ai)
- [Streaming](#streaming)
- [Data Structures](#data-structures)
  - [B Tree](#b-tree)
  - [Radix Trie](#radix-trie)
- [CRDTs](#crdts)
- [Big Data](#big-data)
  - [hadboop](#hadboop)
  - [Spark](#spark)
  - [Message brokrs](#message-brokrs)
  - [Services](#services)
- [Graph systems](#graph-systems)
  - [SQL](#sql-1)
  - [sqlite](#sqlite)
- [Resources](#resources)
  - [Conferences](#conferences)
  - [Misc](#misc)
- [postgres](#postgres)


See also:
- Datalog
- concurrency



# Key Value Store
log structured storage
a log is a append only store
LSM - log structured merge trees. In memory table for writes. Flushed to disk. Multiple read only written to disk, coalesced in background.
sstable
Tombstone records for deletes.
https://www.igvita.com/2012/02/06/sstable-and-log-structured-storage-leveldb/

[What's the big deal about key-value databases like FoundationDB and RocksDB?](https://notes.eatonphil.com/whats-the-big-deal-about-key-value-databases.html) lobster comments https://lobste.rs/s/avljlh/what_s_big_deal_about_embedded_key_value#c_rx0oid

[wide-column store](https://en.wikipedia.org/wiki/Wide-column_store)
[key/value store](https://en.wikipedia.org/wiki/Key%E2%80%93value_database)

- [bigtable](https://en.wikipedia.org/wiki/Bigtable) google internal 
- [dynamo](https://en.wikipedia.org/wiki/Dynamo_(storage_system))

- [cassandra](https://en.wikipedia.org/wiki/Apache_Cassandra) 
- [hbase](https://en.wikipedia.org/wiki/Apache_HBase)


- [leveldb](https://en.wikipedia.org/wiki/LevelDB)
- [redis](https://en.wikipedia.org/wiki/Redis)
- [rocksdb](https://en.wikipedia.org/wiki/RocksDB)

- indexeddb
- [riak](https://en.wikipedia.org/wiki/Riak)


- Foundationdb
- cockroachdb sql database originally on rocksdb now on pebbledb https://www.cockroachlabs.com/blog/pebble-rocksdb-kv-store/
- pebbledb

Embedded key value store. Backing engines. MySql has support for many backing engines

# Algorithms
B-trees

OLTP online transaction processing
OLAP online analytical processing
hyperloglog
bloom filters
cuckoo filter



# Theory

## Conjunctive Queries
Query containment

- See finite model theory

descriptive complexity
NC^0 bounded fan in
AC^0 https://en.wikipedia.org/wiki/AC0 unbounded fan in circuit. Constant height https://en.wikipedia.org/wiki/Circuit_complexity

https://pages.cs.wisc.edu/~paris/cs838-s16/lecture-notes/lecture1.pdf

Foundations of database

## Schema


https://en.wikipedia.org/wiki/Database_normalization

schema is finite set of relation symbol names 
an instance is a set of concrete relations with those symbol names. Sometimes also called a structure

## Functional Dependencies
Armstrong axioms

Normal Formals

Tuple Generating dependencies

## Query Optimization
[Cascades framework](https://www.cse.iitb.ac.in/infolab/Data/Courses/CS632/Papers/Cascades-graefe.pdf)
https://github.com/egraphs-good/egg/discussions/189


Zetasql
calcite

## The Chase
Equality Generating Dependencies
[The Chase Procedure and its Applications in Data Exchange](https://drops.dagstuhl.de/opus/volltexte/2013/4288/pdf/ch01-onet.pdf)

Yisu:
[query optimization](https://dl.acm.org/doi/10.1145/342009.335421)
[data integration](https://drops.dagstuhl.de/opus/volltexte/2013/4288/pdf/ch01-onet.pdf)
[querying incomplete databases](https://dl.acm.org/doi/abs/10.1016/j.is.2009.08.002)
[benchmarking the chase](https://dl.acm.org/doi/abs/10.1145/3034786.3034796)
[chasebench](https://dbunibas.github.io/chasebench/)

Chasefun, DEMOo, Graal, llunatic, pdg, pegasus, dlv, e, rdfox

Stratgeies - (restricted, unrestricted, parallel, skolem, fresh-null

Chase Strategies vs SIPS

[The power of the terminating chase](https://drops.dagstuhl.de/opus/volltexte/2019/10305/pdf/LIPIcs-ICDT-2019-3.pdf)


Is the chase meant to be applied to actual databases, symbolic databases / schema, or other dependencies? 
Is it fair the say that the restricted chase for full dependencies is datalog?

Alice book chapter 8-11

Graal - 
https://github.com/hamhec/DEFT https://hamhec.github.io/DEFT/
defeasible programming http://lidia.cs.uns.edu.ar/delp_client/ Something about extra negation power? Defeatable rules if something contradicts them
Pure is part of graal

llunatic - https://github.com/donatellosantoro/Llunatic

RDfox - https://docs.oxfordsemantic.tech/

dlgp - datalog plus format. Allows variables in head = existentials. Variables in facts.
Notion of constraint `! :- ` and notion of query. Hmm.

Direct modelling of union find in z3? homomorphism is union find

# SQL

sql injection https://ctf101.org/web-exploitation/sql-injection/what-is-sql-injection/
everything is foreign keys? Interning

[Recursive tables](https://www.sqlite.org/lang_with.html) let you do datalog like stuff.

```sql
CREATE TABLE edge(a INTEGER, b INTEGER);
INSERT INTO edge(a,b)
VALUES
    (1,2),
    (2,3),
    (3,4);
SELECT a,b FROM edge;

CREATE TABLE path(a INTEGER, b INTEGER);
--INSERT INTO path
--SELECT * FROM edge;

-- path(x,z) :- edge(x,y), path(y,z).
WITH RECURSIVE
  path0(x,y) AS
    -- SELECT 1,2
    (SELECT a,b FROM edge UNION SELECT edge.a, path0.y FROM edge, path0 WHERE path0.x = edge.b )
  INSERT INTO path SELECT x,y FROM path0;
      
SELECT a,b FROM path;
.quit

```

UF
```
WITH RECURSIVE 
  parent(x,y) AS
  SELECT a, min(b) (SELECT (a,b) FROM eq UNION eq, parent)
```

[python sqlite3 in stdlib](https://docs.python.org/3/library/sqlite3.html)
```python
import sqlite3
con = sqlite3.connect(':memory:')
cur = con.cursor()
# Create table
cur.execute('''CREATE TABLE stocks
               (date text, trans text, symbol text, qty real, price real)''')

# Insert a row of data
cur.execute("INSERT INTO stocks VALUES ('2006-01-05','BUY','RHAT',100,35.14)")

#cur.executemany("insert into characters(c) values (?)", theIter)
for row in cur.execute('SELECT * FROM stocks ORDER BY price'):
  print(row)
```

adapters to python types
https://en.wikipedia.org/wiki/Materialized_view

[sqlite loadable extensions](https://www.sqlite.org/loadext.html)

```python


```

## indices

## views
Saved queries that act as virtual tables
## triggers
This is interesting

## Aggregate functions

## Window Functions





# Ontology Formats

graph database
OWL
RDF
[sparql](https://en.wikipedia.org/wiki/SPARQL)
[sparql slides](https://twitter.com/tayebM/status/1516531076885266432?s=20&t=hmaJXnp6Mp_aUsdRpkOMcQ)
shacl - 

semantic web

[Knowdlege representation handbook](https://dai.fmph.uniba.sk/~sefranek/kri/handbook/handbook_of_kr.pdf)
Course https://web.stanford.edu/class/cs227/Lectures/lec02.pdf very similar to bap knoweldge base

# Optimal Joins
[worst case optimal join algorithm](https://cs.stanford.edu/people/chrismre/papers/paper49.Ngo.pdf)
[leapfrog triejoin](https://arxiv.org/pdf/1210.0481v5.pdf)
https://github.com/frankmcsherry/blog/blob/master/posts/2018-05-19.md
Dovetail join - relational ai unpublished. Julia specific ish? https://relational.ai/blog/dovetail-join
use sparsity of all relations to narrow down search
Worst case optiomal join Ngo pods 2012
leapfrog triejoin simpel worst case icdt 2015
worst case optimal join for sparql
worst case optimal graph joins in almost no space
Correlated subqueries:
unnesting arbitrary queries
How materializr and other databases optimize sql subqueries

[genlteish intro to worst case optimal joins](https://twitter.com/justinjaffray/status/1531312730824536064?s=20&t=-IHVNfpCMKlhva0T8ctWXA)

[Adopting Worst-Case Optimal Joins in Relational Database Systems](https://db.in.tum.de/~freitag/papers/p1891-freitag.pdf) tries
[The Adaptive Radix Tree: ARTful Indexing for Main-Memory Databases](https://db.in.tum.de/~leis/papers/ART.pdf)
[Persistent Storage of Adaptive Radix Trees in DuckDB](https://duckdb.org/2022/07/27/art-storage.html)


[oltp indices 2](https://www.youtube.com/watch?v=N6rhECUjdaI&t=1045s&ab_channel=CMUDatabaseGroup)

[umbra](https://db.in.tum.de/~freitag/papers/p29-neumann-cidr20.pdf) spiritual successor to hyper. Hybridizes an in memory system to also work off ssd.


# Vectorized Execution
[cmu adavanced course lecture](https://www.youtube.com/watch?v=7hgZKrFXYNs&ab_channel=CMUDatabaseGroup)
[Rethinking SIMD Vectorization for In-Memory Databases](https://15721.courses.cs.cmu.edu/spring2019/papers/20-vectorization1/p1493-polychroniou.pdf)

masked/selective load
masked/selective store
scatter 
gather

selection:
branched vs branchless
branched checks condition to see if should copy row out
branchless writes but only increments index of storage by one if condition is met. I mean. There is a "branch" in this. But I see your point


[EmptyHeaded: A Relational Engine for Graph Processing](https://ppl.stanford.edu/papers/emptyheaded.pdf) "generalized hypertree decomposition" ? https://github.com/HazyResearch/EmptyHeaded

[levelheaded](https://aberger.site/levelheaded.pdf) linear algerba stuff?

# Multi Version Concurrency Control
https://en.wikipedia.org/wiki/Multiversion_concurrency_control


# Duckdb
https://duckdb.org/
sqlite for olap
columnar
```python
import duckdb
con = duckdb.connect(database=':memory:')
import pandas as pd
test_df = pd.DataFrame.from_dict({"i":[1, 2, 3, 4], "j":["one", "two", "three", "four"]})
con.execute('SELECT * FROM test_df')
#print(con.fetchall())
print(con.fetchdf())

add_df = pd.DataFrame(columns=["x","y","z"])
print(add_df)
counter = 0
def add(x,y):
  global counter, add_df
  cond = add_df["x"] == x #& add_df["y"] == y
  df = add_df[cond]
  if not df.empty:
    return add_df["z"][0]
  else:
    z = counter
    add_df.append((x,y,z))
    counter += 1
    return z

print(add(-1,-2))

```

```python
import duckdb
con = duckdb.connect(database=':memory:')
con.execute("CREATE TABLE root (x INTEGER, y INTEGER);")
# "don't use execute many"
con.executemany("INSERT INTO root VALUES (?, ?)", [(1,1),(2,2),(3,3),(1,2),(2,3)])
con.execute("""
SELECT x, max(y)
    FROM root
    GROUP BY x;""")
print(con.fetchall())



#con.execute("""
#UPDATE root a
#  INNER JOIN root b 
#  ON a.y = b.x
#  SET a.y = b.y""")
#print(con.fetchall())

#con.execute("""
#UPDATE root c
#  SET y = max(b.y)
#    FROM root a
#    INNER JOIN root b ON a.x = c.x AND a.y = b.x
#    """)
#print(con.fetchall())

con.execute("""
WITH root2(x1,y1) AS (
  SELECT a.x, max(b.y)
    FROM root a, root b
    WHERE a.y = b.x
    GROUP BY a.x
)
UPDATE root
  SET y = max(b.y)
  FROM root a
  INNER JOIN root b
  ON a.y = b.x
  GROUP BY a.x;
    """)
print(con.fetchall())

con.execute("""
SELECT a.x, max(b.y)
    FROM root a, root b
    WHERE a.y = b.x
    GROUP BY a.x;""")
print(con.fetchall())


```

catalog multiversion concrruncy control
cimpressed execution binder


# Relational AI
https://www.youtube.com/watch?v=WRHy7M30mM4&ab_channel=CMUDatabaseGroup

snowflake
databricks
bigquery
dbt 
fivetran

data apps - dapps

lookml
sigma
legend

Resposnive compilter - matsakis
salsa.jl
umbra/leanstore

incremental
COnvergence of datalog over presmeirings
differential dataflor cidr2013
reconciling idfferences 2011 Green
F-IVM incrmenetal view mantinance with triple lock fotrization benefits

systemml vecame apache systemds https://systemds.apache.org/

Semantic optimization
FAW question asked frequence : Ngo Rudra PODS 2016
What do shannon type ineuqlaities submodular width and disjunctive datalog have to do with one another pods 2017
precise complexity analysis for efficient datalog queries ppdp 2010
functional aggregate queries with additive inequalities
convergence of dtalog over pr-esemirign

Relational machine learning
Layered aggregate engine for analystics worloads schelich olteanu khamis
leanring models over relational data using sparse tenosrs
The relational data borg is learning olteanu vldb keynote
sturcture aware machine learning over multi relational database
relational know graphs as the ofundation for artifical intelligence
km-means: fast clustering for relational data
https://arxiv.org/abs/1911.06577 Learning Models over Relational Data: A Brief Tutorial


duckdb for sql support
calcite
postgresql parser

Fortress library traits. OPtimization and parallelism
https://relational.ai/blog/categories/research

https://arxiv.org/abs/2004.03716 triangle view mantenance
# Streaming
[streaming 101](https://www.oreilly.com/radar/the-world-beyond-batch-streaming-101/)
unbounded data

https://en.wikipedia.org/wiki/Stream_processing

lambda architecture - low latency inaccurate, then batch provides accurate

event time vs processing time

Watermark

Flink
Apache Beam
millwheel
spark streaming

https://materialize.com/blog

# Data Structures

## B Tree
Bw-tree
[The B-Tree, LSM-Tree, and the Bw-Tree in Between](https://photondb.io/2022/08/15/bw-tree.html)
[open bw-tree 2018](https://www.cs.cmu.edu/~huanche1/publications/open_bwtree.pdf)
## Radix Trie


# CRDTs
Conflict Free replicated datatypes
<https://crdt.tech/> martin Kleppmann

CRDT of string - consider fractional positions. Tie breaking. Bad interleaving problem
unique identifiers

- LSeq
- RGA
- TreeSeq

https://www.inkandswitch.com/peritext/ crdt rich text

https://github.com/josephg/diamond-types
https://josephg.com/blog/crdts-go-brrr/

https://github.com/yjs/yjs

[automerge: library of data structures for collab applications in javascript](https://github.com/automerge/automerge) https://mobiuk.org/abstract/S4-P5-Kleppmann-Automerge.pdf
local first. use local persistent storage. git for your app's data. rust implementation?


[isabelle crdt](https://github.com/trvedata/crdt-isabelle)
[I was wrong. CRDTs are the future](https://news.ycombinator.com/item?id=31049883)

[Conflict-free Replicated Data Types”](https://arxiv.org/pdf/1805.06358.pdf)
[“A comprehensive study of Convergent and Commutative Replicated Data Types](https://hal.inria.fr/inria-00555588/document)

Operational Transformation - sequences of insert and delete. Moves possibly.

delta-based vs state-based https://bartoszsypytkowski.com/the-state-of-a-state-based-crdts/

counters

json crdt for vibes patches?

Tree move op. Create delete subtrees.

[Synthesizing CRDTs from Sequential Data Types with Verified Lifting](https://twitter.com/ShadajL/status/1544375739046211584?s=20&t=-v_26IaEHywfZUA_4b8T8g)
https://arxiv.org/abs/2205.12425


# Big Data
Spark
Hadoop
MapReduce
Dask
Flink
Storm

Mahout
Vowpal Wabbit
## hadboop

Giraph


## Spark
https://en.wikipedia.org/wiki/Apache_Spark
Databricks - company
bigdatalog https://www.cis.upenn.edu/~susan/cis700/Papers/BigDataAnalyticsSPARK.pdf https://github.com/ashkapsky/BigDatalog
MLlib
spark streaming
graphx


## Message brokrs
RabbitMQ
Kafka

## Services
BigQuery
Snowflake
Azure AWS 


# Graph systems
It isn't that relational systems can't express graph problems. But maybe graph systems are more optimized for the problem
neo4j
Giraph
Powergraph
graphrex
graphx
myria
graphchi
xsteam
gridgraph
graphlab



## SQL
- `create table`
- `create index`
- `explain query plan` I saw `explain analyze` elsewhere
- `select`
- `vacuum` - defrag and gabrage collect the db
- `begin transaction`
## sqlite
[sqlite commands](https://www.sqlitetutorial.net/sqlite-commands/) that are interesting 
- `.help`
- `.dump`
- `.tables`
- `.schema`
- `.indexes`
- `.expert` suggests indices?




# Resources
## Conferences
- SIGMOD PODS https://sigmod.org/pods-home/ pods uutorials https://sigmod.org/pods-home/pods-tutorials/ [Testy of time awards](https://sigmod.org/pods-home/acm-pods-alberto-o-mendelzon-test-of-time-award/) Cool stuff in here.
- VLDB
- HYTRADBOI https://www.hytradboi.com/ also very cool stuff.
## Misc
[SQL/DB learning resources](https://twitter.com/craigkerstiens/status/1568269750693773313?s=20&t=Ed04dBodGtW0kFSYL76bNQ)

[use the index luke](https://use-the-index-luke.com/)
[sqlbolt](https://sqlbolt.com/) = interactive sql tutorial

[the art of postgresql](https://theartofpostgresql.com/) a book.
[select star sql](https://selectstarsql.com/)

[schemaverse](https://schemaverse.com/) a space battle game written in sql
  
[SQLite: Past, Present, and Future](https://www.vldb.org/pvldb/vol15/p3535-gaffney.pdf)

[Datavases, types, and the relational model The third manifesto](https://www.dcs.warwick.ac.uk/~hugh/TTM/DTATRM.pdf)

[how query engines work](https://leanpub.com/how-query-engines-work) andy grove

[database internals book](https://twitter.com/therealdatabass)

[database design and implementation](https://link.springer.com/book/10.1007/978-3-030-33836-7)

[duckdb](https://twitter.com/teej_m/status/1516864922784702469?s=20&t=hmaJXnp6Mp_aUsdRpkOMcQ) embedded like sqlite?

[https://xtdb.com/](XTDB is a general-purpose bitemporal database for SQL, Datalog & graph queries.)

[Conjunctive-query containment and constraint satisfaction](https://dl.acm.org/doi/10.1145/275487.275511)

Designing Data intensive systems martin kleppmann

[scalability but at what cost?](http://www.frankmcsherry.org/assets/COST.pdf) big systems vs laptops.


[Data integration the relational logic approach](http://logic.stanford.edu/dataintegration/)

[postgres indexes for newbies](https://blog.crunchydata.com/blog/postgres-indexes-for-newbies)
[postgres tutorial](https://www.postgresqltutorial.com/)
[raytracer in sql](https://github.com/chunky/sqlraytracer)
[advent of code sql(https://news.ycombinator.com/item?id=29467671)]
[sqllancer](https://github.com/sqlancer/sqlancer) detecting lgoic bugs in dbms

 - Differential Datalog
- CRDTs
- Differential Dataflow
- Nyberg Accumulators
- Verkle Trees
- Cryptrees
- Byzantine Eventual Consistency
- Self-renewable hash chains
- Binary pebbling

https://github.com/dbuenzli/rel

Ezra Cooper. The Script-Writer’s Dream: How to Write Great SQL in Your Own Language, and Be Sure It Will Succeed. 2009. Full text

James Cheney et al. A practical theory of language-integrated query. 2013. Full text

Suzuki et al. Finally, safely-extensible and efficient language-integrated query. 2016. Full text

Oleg Kiselyov et al. Sound and Efficient Language-Integrated Query -- Maintaining the ORDER. 2017. Full text

[DBSP: Automatic Incremental View Maintenance for Rich Query Languages - mcsherry et al](https://arxiv.org/abs/2203.16684)

[pavlo advanced databases](https://15721.courses.cs.cmu.edu/spring2020/schedule.html)

[awesome database learning](https://github.com/pingcap/awesome-database-learning)

[database architects blogs](https://databasearchitects.blogspot.com/)

https://www.reddit.com/r/databasedevelopment/

https://twitter.com/phil_eaton

[database internals](https://www.databass.dev/)

[Ask HN: What could a modern database do that PostgreSQL and MySQL can't](https://news.ycombinator.com/item?id=28425379)

[postgres internals book](https://postgrespro.com/blog/pgsql/5969682)

[advanced sql course](https://www.youtube.com/playlist?list=PL1XF9qjV8kH12PTd1WfsKeUQU6e83ldfc)

[roaring bitmaps](https://twitter.com/phil_eaton/status/1567610292586045443?s=20&t=Ed04dBodGtW0kFSYL76bNQ) https://vikramoberoi.com/a-primer-on-roaring-bitmaps-what-they-are-and-how-they-work/
Switches out storage method and different scales and density.

[](https://modern-sql.com/)

```sql
SELECT 40 + 2;
```

```sql
CREATE TABLE T (a int PRIMARY KEY, -- implies not null
 b bool, c text, d int);

-- CREATE TYPE mytype AS (a bool, b text);

INSERT INTO T VALUES
(1,true, "hi", 3),
(2,true, "hi", 3)
;

-- INSERT INTO T TABLE T;

SELECT myrow.* -- 2 returns row variable
FROM T AS myrow;-- 1 binds myrow


SELECT myrow.* -- 2 returns row variable
FROM T AS myrow WHERE myrow.a = myrow.a;

DROP TABLE IF EXISTS T;

--SELECT * FROM T;

-- can label columns
SELECT 40 + 2 AS firstcol, "dog" || "store" AS secondcol;

VALUES (10), (20); -- values may be used anywhere sql expects a table


SELECT * FROM (VALUES (10,20), (0,10)) AS myrow(x,y); 
```
Scalar subqueries - subqueries that return a single row may be considered as scalar values

From binds below, even though it's kind of a for loop.
[row for row in table] I guess this also reverses order.

Order by expressions. So we coukd have many more ordering constraints than columns for xample

Select distinct on. Returns first row in each group.


agregates bool_and bool_or (forall and exists)


Group by - wadler. Changing type of row entry to bag(row entry) 

ALL bag semantics, no all is set semantics

```sql
WITH RECURSIVE 
  series(i) as (
    VALUES (0)
    UNION
    SELECT t.i + 1 FROM
      series as t where t.i < 10
  )
 SELECT * FROM series;

```

```sql
WITH RECURSIVE
  root(i,j) AS (
    SELECT foo.i, max(foo.j) 
    FROM (VALUES (1,1), (2,1), (3,3)) AS foo(i,j)
          --UNION 
          --(SELECT i, k FROM root AS (i,j), root as (j1,k) where j = j1))
          )
    SELECT * from root;

```

```sql
SELECT *
  FROM (VALUES (1,1), (2,1), (3,3)) AS foo(i,j);

```

```sql
SELECT (SELECT 42) * 2; -- this works. There is broadcasting of sorts

```

[Does sql need help](https://news.ycombinator.com/item?id=32799920)

Views

# postgres
`sudo -u postgres psql`
