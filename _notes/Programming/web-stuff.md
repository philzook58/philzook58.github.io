---
layout: post
title: Web Stuff
---
- [Networking](#networking)
- [HTTP](#http)
- [HTML](#html)
- [CSS](#css)
- [Javascript](#javascript)
  - [Frameworks](#frameworks)
- [Serving](#serving)
  - [Frameworks](#frameworks-1)
    - [Template Engines](#template-engines)
  - [WebServers](#webservers)
    - [Apache](#apache)
    - [Nginx](#nginx)
  - [Databases](#databases)
  - [CGI](#cgi)
  - [WSGI](#wsgi)
  - [Docker](#docker)
  - [Kubernetes](#kubernetes)
  - [Web platforms](#web-platforms)
- [SVG](#svg)
- [Misc](#misc)

# Networking

- TCP/IP
- DNS

# HTTP

# HTML

Uhhhh. Is there anything interesting to say here?
You can make nested tags.

# CSS

[simple web frontend stuff](https://news.ycombinator.com/item?id=32011439)
[simple css to look good everywhere](https://news.ycombinator.com/item?id=32972004)
[web design in 4 minutes](https://jgthms.com/web-design-in-4-minutes/)
cssbed
htmx

flexbox

[cassius](https://cassius.uwplse.org/) vizassert. Constraint based. Z3 layout? Troika - a proof assistant version. Pavel and Zach

Get some nicer default styling, often some kind of grid system for layout, mobile formatting etc.

- [bootstrap](https://getbootstrap.com/)
- Foundation
- Tailwind CSS
- Material UI

# Javascript

- Javascript should probably be in a languages document
- Typescript is a typed javascript thing
- Webpack
- npm
- WASM - see wasm notes
- node, deno, bun
- engines - V8, spidermonkey, quickjs
- JSON

[Javascript without a build system](https://jvns.ca/blog/2023/02/16/writing-javascript-without-a-build-system/)

## Frameworks

What do these even do for you? Well, they are ecosystems of widgets and opinionated ways of organizing a webpage, so that's nice.

- React
- [Vue](https://vuejs.org/)

<https://threlte.xyz/> 3d web apps
<https://svelte.dev/>

# Serving

- Single page vs server side rendering stuff

- OpenAPI, Swagger

## Frameworks

- PHP
- Django - python
- Express - node
- Ruby on rails

### Template Engines

These are often tied to a particular framework. It's interesting that these template systems can find their way elsewhere. You could use them for code metaprogramming for example. Isn't that twisted and fun?

- Jinja
- Handlebar

## WebServers

### Apache

<https://httpd.apache.org/>
Apache is super powerful.

Modules are libraries that add functionality to apache

Running this way is so hard

```bash
echo "Hello World" > /tmp/index.html
echo "
ServerName localhost
IncludeOptional mods-enabled/*.load
IncludeOptional mods-enabled/*.conf
CustomLog /tmp/access.log combined
ErrorLog /tmp/error.log
#LoadModule mpm_event_module modules/mod_mpm_event
#LoadModule mpm_prefork_module modules/mod_mpm_prefork.so
Listen 8080
Redirect "/" "http://otherserver.example.com/"
" > /tmp/httpd.conf
apache2 -f /tmp/httpd.conf -k start
# apache2ctl

#cat /etc/apache2/apache2.conf # good to look at the default config
#apache2 -l # list modules
```

### Nginx

[nginx playgroud](https://jvns.ca/blog/2021/09/24/new-tool--an-nginx-playground/)

```bash
echo "

" > /tmp/nginx.conf
cat /etc/nginx/nginx.conf # good to look at the default config
#nginx -c /tmp/nginx.conf
nginx -h
# -t test, -s signal, -c cong, -g directovies.
```

## Databases

- See database notes

## CGI

## WSGI

## Docker

## Kubernetes

## Web platforms

- AWS
- Azure
- GCP

# SVG

<svg>
    <rect x="52" y="51" width="138" height="91" fill="rgb(255, 100, 255)"/>
</svg>

![a blue square](/assets/test.drawio.svg)

Hmm. Inline svg. svg preview of links. Image preview.

Ok so make a foo.drawio.svg fle somewhere, then drag and drop a link into my notes.

# Misc
