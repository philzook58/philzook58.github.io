---
layout: page
title: Notes
permalink: /notes/
---
<ul>
{% for item in site.notes %}
  <li><a href="{{ item.url }}">{{ item.title }}</a></li>
{% endfor %}
</ul>