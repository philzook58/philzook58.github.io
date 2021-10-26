---
layout: page
title: Notes
permalink: /notes/
---
More fluid than posts. Unfinished thoughts. Link Dumps. I will hopefully continually rearrange and crosslink these.
<ul>
{% for item in site.notes %}
  <li><a href="{{ item.url }}">{{ item.title }}</a></li>
{% endfor %}
</ul>