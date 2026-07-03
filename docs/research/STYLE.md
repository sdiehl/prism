# Research Doc Style Guide

Conventions for markdown files under `docs/research/`.

## Links

- **No bare URLs.** Every URL must be wrapped in `[descriptive text](url)`.
- **Link text** should be descriptive, concise, and understandable out of context. You do not have to use the full formal title of a document; use good judgment to keep it readable and highly scannable (see the [link writing guidelines](https://www.nngroup.com/articles/writing-links/) from Nielsen Norman Group):
  - **Descriptive**: Anchor text must carry "information scent" (what the user gets when they click). Avoid generic labels like "here", "read more", or "click here".
  - **Frontloaded**: Place the most important keywords at the start of the link text so users can scan it quickly (users look primarily at the first 2 words of a link).
  - **Context-Free**: The link text must make sense on its own without requiring the surrounding sentence to be read.
- **Citations and Metadata**: Date/author/version info goes **outside** the link text. For reference lists, citations should start with the year (newest first):
  ```markdown
  - [Introducing Prism](https://www.stephendiehl.com/posts/prism/) — stephendiehl.com, 2025
  - 2016 — Haller & Loiko. ["LaCasa"](https://doi.org/10.1145/2983990.2984042). _OOPSLA 2016._
  - 2019 — Clebsch et al. ["Protocols for Concurrent Reference Counting"](https://doi.org/10.4230/LIPIcs.ECOOP.2019.25). _EcoOP 2019._
  ```
  For academic papers, the title (in quotes) is the primary hyperlink. The DOI identifier (e.g., `DOI: [10.1145/...](https://doi.org/...)`) may be explicitly listed as a visible secondary link for citation completeness, but the title remains the main, scannable clickable element. Do not expect readers to click the raw DOI links.
- **Intra-doc links** within `docs/` use markdown relative paths. Use a clean descriptive name, rather than the raw filename:
  - Yes: `[the Passable datatype design](01-passable-datatype.md)`
  - No: `[01-passable-datatype.md](01-passable-datatype.md)`
- **Metadata headers** use bullet lists, not `**Label**: [link](...)`:
  ```markdown
  - [Akka Core documentation](https://doc.akka.io/libraries/akka-core/current/)
  - [Pekko documentation](https://pekko.apache.org/docs/pekko/current/)
  ```

## File Naming

- **No `README.md`** — Obsidian renders it poorly. Use `00-<topic>.md` instead (e.g., `00-ocapn-actors.md`).
- **Prior art abstracts / literature searches** start with their **seminal year** (the year the topic or system was introduced/popularized, rather than the year of the most recent release or material surveyed). This preserves a clean historical timeline of the lineage of ideas in the file explorer:
  - `1998-erlang-beam.md` (Erlang open-sourced)
  - `2009-scala-akka.md` (Akka introduced)
  - `2013-monte-masque-spotter.md` (Monte introduced)
  - `2015-pony.md` (Pony first published)
  - `2019-goblins.md` (Goblins development started)
  - `2023-ocapn-protocol.md` (OCapN standardization push)
  - `2025-prism-language.md` (Prism introduced; prior to this research but baseline of it)
- **Goals / designs / explorations / issues** start with a two-digit number: `nn-<name>.md` (e.g., `01-passable-datatype.md`, `02-netlayers.md`). Keep numbers sequential.
- Alphabetical sorting in Obsidian naturally groups goals/explorations (`nn-`) first, followed by historical literature/prior art (`YYYY-`).
