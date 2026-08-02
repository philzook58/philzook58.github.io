---
layout: page
title: LongForm
permalink: /longform/
folders:
  - arip
  - physoks
  - tpik
---

{% for folder in page.folders %}
<h2>{{ folder }}</h2>
<ul>
  {% assign prefix = "longform/" | append: folder | append: "/" %}
  {% for item in site.pages %}
    {% if item.path contains prefix %}
      {% if item.title %}
        <li><a href="{{ item.url | relative_url }}">{{ item.title }}</a></li>
      {% endif %}
    {% endif %}
  {% endfor %}
</ul>
{% endfor %}
