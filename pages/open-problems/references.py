#!/usr/bin/env python3
"""Format the bibliography of the list of open problems.

Reads `references.yml`, converted to JSON by `yq`, on the standard input, and writes to the standard
output a JSON object from every citation key to its entry formatted in the style of APA, as HTML:

    yq --output-format=json . references.yml | python3 pages/open-problems/references.py > pages/open-problems/references.json

`index.html` shows the entries of the keys cited by a docstring at the end of the list.
"""

import json
import sys
from html import escape


def clean(text):
    """A title or a name without the braces that protect capitals in BibTeX."""
    return text.replace("{", "").replace("}", "").strip()


def as_list(value):
    return value if isinstance(value, list) else [value]


def initials(given):
    """`Marie-Françoise` becomes `M.-F.`, and `Alex J.` becomes `A. J.`."""
    return " ".join("-".join(part[0] + "." for part in word.split("-") if part)
                    for word in given.split())


def author_name(name):
    """`Surname, Given` as `Surname, G.`."""
    surname, _, given = clean(name).partition(",")
    return f"{surname.strip()}, {initials(given)}" if given.strip() else surname.strip()


def editor_name(name):
    """`Surname, Given` as `G. Surname`."""
    surname, _, given = clean(name).partition(",")
    return f"{initials(given)} {surname.strip()}" if given.strip() else surname.strip()


def join_names(names, comma_before_and):
    if len(names) <= 2 and not comma_before_and:
        return " & ".join(names)
    if len(names) == 1:
        return names[0]
    return ", ".join(names[:-1]) + ", & " + names[-1]


def authors(entry):
    return join_names([author_name(a) for a in as_list(entry["author"])], comma_before_and=True)


def editors(parent):
    names = [editor_name(e) for e in as_list(parent["editor"])]
    return join_names(names, comma_before_and=False) + (" (Eds.)" if len(names) > 1 else " (Ed.)")


def ordinal(n):
    suffix = "th" if 10 <= n % 100 <= 20 else {1: "st", 2: "nd", 3: "rd"}.get(n % 10, "th")
    return f"{n}{suffix}"


def pages(entry):
    """`143-161` as `pp. 143–161`, and `7` as `p. 7`."""
    pr = str(entry["page-range"]).replace("-", "–")
    return ("pp. " if "–" in pr else "p. ") + pr


def sentence(text):
    """`text` ended by a full stop, unless it ends with a punctuation mark already."""
    return text if text.endswith((".", "?", "!")) else text + "."


def publisher(entry):
    """The publisher of `entry`, with the name of an organization as a fallback."""
    p = entry.get("publisher")
    if isinstance(p, dict):
        p = p.get("name")
    return p or entry.get("organization")


def link(entry):
    """The link at the end of a reference: the DOI, else the URL, else the arXiv page."""
    sn = entry.get("serial-number") or {}
    url = (f"https://doi.org/{sn['doi']}" if "doi" in sn
           else entry.get("url") or (f"https://arxiv.org/abs/{sn['arxiv']}" if "arxiv" in sn else None))
    if url is None:
        return ""
    return f' <a href="{escape(url)}">{escape(url)}</a>'


def title_html(entry, italic):
    title = escape(clean(entry["title"]))
    return f"<i>{title}</i>" if italic else title


def number(entry, parent, field):
    """The volume or the issue of `entry`, which a bibliography may give on its parent."""
    value = entry.get(field) or parent.get(field)
    return None if value is None else str(value).replace("-", "–")


def is_chapter(entry):
    """Whether `entry` is a part of a book: a chapter, or an article filed in an anthology."""
    parent = entry.get("parent") or {}
    return entry["type"] == "Chapter" or (
        entry["type"] == "Article" and parent.get("type") in ("Anthology", "Proceedings"))


def container(entry):
    """The part after the title of an article, a chapter or a report."""
    parent = entry.get("parent")
    kind = "Chapter" if is_chapter(entry) else entry["type"]
    if kind == "Article" and parent:
        volume, issue = number(entry, parent, "volume"), number(entry, parent, "issue")
        volume = (f", <i>{volume}</i>" if volume else "") + (f"({issue})" if issue else "")
        pg = f", {pages(entry).split(' ', 1)[1]}" if entry.get("page-range") else ""
        return sentence(f"<i>{escape(clean(parent['title']))}</i>{volume}{pg}")
    if kind == "Chapter" and parent:
        details = []
        if "edition" in parent:
            details.append(f"{ordinal(parent['edition'])} ed.")
        if "volume" in parent:
            details.append(f"Vol. {parent['volume']}")
        if entry.get("page-range"):
            details.append(pages(entry))
        who = f"{escape(editors(parent))}, " if "editor" in parent else ""
        text = f"In {who}<i>{escape(clean(parent['title']))}</i>"
        if details:
            text += f" ({escape(', '.join(details))})"
        pub = publisher(parent)
        return sentence(text) + (f" {sentence(escape(pub))}" if pub else "")
    if kind == "Article":
        arxiv = (entry.get("serial-number") or {}).get("arxiv")
        return f"arXiv:{escape(arxiv)}." if arxiv and not (entry.get("serial-number") or {}).get("doi") else ""
    return ""


def format_entry(entry, year):
    kind = "Chapter" if is_chapter(entry) else entry["type"]
    head = f"{escape(authors(entry))} ({year})."
    if kind in ("Article", "Chapter"):
        parts = [head, sentence(title_html(entry, italic=False)), container(entry)]
        # An article known only by its arXiv number is cited by it, as a link.
        if kind == "Article" and not entry.get("parent"):
            sn = entry.get("serial-number") or {}
            if "arxiv" in sn and "doi" not in sn:
                return " ".join(parts[:2]) + link(entry)
        return " ".join(p for p in parts if p) + link(entry)
    if kind == "Book":
        pub = publisher(entry)
        return " ".join(p for p in [head, sentence(title_html(entry, italic=True)),
                                    sentence(escape(pub)) if pub else ""] if p) + link(entry)
    # Reports, theses and notes: a standalone work with a description after the title.
    note = entry.get("note")
    genre = entry.get("genre")
    org = entry.get("organization")
    title = title_html(entry, italic=True)
    if kind == "Report" and note:
        title += f" ({escape(note)})"
        org_part = sentence(escape(org)) if org else ""
    elif kind == "Thesis":
        title += f" [{escape(', '.join(p for p in [note, org] if p))}]"
        org_part = ""
    else:
        description = genre or note
        if description:
            title += f" [{escape(description)}]"
        org_part = sentence(escape(org)) if org and genre else ""
    return " ".join(p for p in [head, sentence(title), org_part] if p) + link(entry)


def years(entries):
    """The year of each entry, with `a`, `b`, … after it when one author wrote two in a year."""
    groups = {}
    for key, e in entries.items():
        groups.setdefault((authors(e), e["date"]), []).append(key)
    result = {}
    for (_, year), keys in groups.items():
        keys.sort()
        for i, key in enumerate(keys):
            result[key] = f"{year}{chr(ord('a') + i)}" if len(keys) > 1 else str(year)
    return result


def main():
    entries = json.load(sys.stdin)
    year = years(entries)
    json.dump({key: format_entry(e, year[key]) for key, e in entries.items()},
              sys.stdout, ensure_ascii=False, indent=2)
    print()


if __name__ == "__main__":
    main()
