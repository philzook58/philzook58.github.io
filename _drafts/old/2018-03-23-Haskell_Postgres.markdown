---
author: philzook58
comments: true
date: 2018-03-23 14:42:46+00:00
layout: post
link: https://www.philipzucker.com/?p=1015
published: false
slug: Haskell Postgres
title: Haskell Postgres
wordpress_id: 1015
---

There are a lot of options:

Postgres-simple

opaleye - builds on top of postegres-sql

persistent

[esqueleto - builds on top of persistent](https://hackage.haskell.org/package/esqueleto)

postgrest - a framework for building a REST API directly to postgres database.  Written in Haskell, but not particularly a haskell library

A technqiue I like to use is go onto hackage and sort by downloads. That tends to push the popular stuff to the top.

Persistent has a chapter in the Yesod book.

https://www.yesodweb.com/book/persistent

A useful example project:

https://github.com/parsonsmatt/servant-persistent

https://gist.github.com/creichert/2127b23766a25b183442

Persistent is heavily leaning on template-haskell.

I'm not sure I like that.



Ok.

So I need a pool of connections

withPostgresqlPool (connStr ) 10 action

is gonna run the action with supplied pool

The Config.hs createst he pool iun the servant example
<table class="highlight tab-size js-file-line-container" data-tab-size="4" >
<tbody >
<tr >

<td id="LC31" class="blob-code blob-code-inner js-file-line" >doMigrations :: SqlPersistT IO ()
</td>
</tr>
</tbody>
</table>
<table class="highlight tab-size js-file-line-container" data-tab-size="4" >
<tbody >
<tr >

<td id="LC32" class="blob-code blob-code-inner js-file-line" >doMigrations = runMigration migrateAll
</td>
</tr>
</tbody>
</table>
<table class="highlight tab-size js-file-line-container" data-tab-size="4" >
<tbody >
<tr >

<td id="LC33" class="blob-code blob-code-inner js-file-line" >
</td>
</tr>
</tbody>
</table>
<table class="highlight tab-size js-file-line-container" data-tab-size="4" >
<tbody >
<tr >

<td id="LC34" class="blob-code blob-code-inner js-file-line" >runDb :: (MonadReader Config m, MonadIO m) => SqlPersistT IO b -> m b
</td>
</tr>
</tbody>
</table>
<table class="highlight tab-size js-file-line-container" data-tab-size="4" >
<tbody >
<tr >

<td id="LC35" class="blob-code blob-code-inner js-file-line" >runDb query = do
</td>
</tr>
</tbody>
</table>
<table class="highlight tab-size js-file-line-container" data-tab-size="4" >
<tbody >
<tr >

<td id="LC36" class="blob-code blob-code-inner js-file-line" >pool <- asks configPool
</td>
</tr>
</tbody>
</table>
liftIO $ runSqlPool query pool



Hes using SqlPersistT

Nevermind. There is abetter example at the bottom of the perissitent book page



https://www.codementor.io/engineerapart/getting-started-with-postgresql-on-mac-osx-are8jcopb

CREATE ROLE test with LOGIN PASSWORD 'test';

GRANT ALL PRIVILEGES ON DATABASE testdb TO test;

\du

\list lists db

\connect

\q quits

\dt list tables



command line utility

    
    <code class="hljs ceylon">createdb <span class="hljs-keyword">super</span><span class="hljs-number">_</span>awesome<span class="hljs-number">_</span>application -U patrick</code>




lot's of juicy bits in

https://hackage.haskell.org/package/persistent-2.8.1/docs/Database-Persist-Sql.html



Getting dockerized postgres up

    
    version: "3"
    services:
    
    
      db:
        image: postgres:latest
        restart: unless-stopped
        ports:
         - "5433:5432"
        volumes:
          - ./pgdata/:/var/lib/postgresql/data
        environment:
          POSTGRES_PASSWORD: ${PGPASS}
          POSTGRES_DB: dbname
          POSTGRES_USER: example_user
    
    # psql postgres -U postgres -h localhost -p 5433
    
    #POSTGRES_USER
    #https://docs.docker.com/samples/library/postgres/#-via-docker-stack-deploy-or-docker-compose


useful info : https://docs.docker.com/samples/library/postgres/#postgres_password




