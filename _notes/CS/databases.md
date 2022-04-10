---
layout: post
title: Databases
---

- [Schema](#schema)
  - [Functional Dependencies](#functional-dependencies)
  - [Query Optimization](#query-optimization)
  - [The Chase](#the-chase)
- [Ontology Formats](#ontology-formats)
- [Optimal Joins](#optimal-joins)
- [Streaming](#streaming)
  - [Schema](#schema-1)
  - [SQL](#sql)
  - [sqlite](#sqlite)
- [Resources](#resources)


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

https://en.wikipedia.org/wiki/Materialized_view

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

## Query Optimization
[Cascades framework](https://www.cse.iitb.ac.in/infolab/Data/Courses/CS632/Papers/Cascades-graefe.pdf)

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