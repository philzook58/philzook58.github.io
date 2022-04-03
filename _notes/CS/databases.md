---
layout: post
title: Databases
---

See also:
- Datalog


https://en.wikipedia.org/wiki/Database_normalization

everything is foreign keys? Interning

```sql
CREATE TABLE edge(a INTEGER, b INTEGER);
INSERT INTO edge(a,b)
VALUES
    (1,2),
    (2,3),
    (3,4);
SELECT a,b FROM edge;
.quit

```


## indices

## views
Saved queries that act as virtual tables
## triggers
This is interesting

## Aggregate functions

## Window Functions

# Schema
## Functional Dependencies
Armstrong axioms

Normal Formals

Tuple Generating dependencies

## The Chase
Equality Generating Dependencies


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


# Ontology Formats

graph database
OWL
RDF
[sparql](https://en.wikipedia.org/wiki/SPARQL)
shacl - 

semantic web

# Streaming
[streaming 101](https://www.oreilly.com/radar/the-world-beyond-batch-streaming-101/)
unbounded data

lambda architecture - low latency inaccurate, then batch provides accurate

event time vs processing time

Watermark

Flink
Apache Beam
millwheel
spark streaming



## Schema






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
[Data integration the relational logic approach](http://logic.stanford.edu/dataintegration/)

[postgres indexes for newbies](https://blog.crunchydata.com/blog/postgres-indexes-for-newbies)
[postgres tutorial](https://www.postgresqltutorial.com/)
[raytracer in sql](https://github.com/chunky/sqlraytracer)

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
- 