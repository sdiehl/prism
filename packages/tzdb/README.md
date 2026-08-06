# tzdb for Prism

Deterministic timezone arithmetic over a pinned, curated zone table. The operating system's timezone database is an ambient input, so this package refuses to consult it: the zone data is ordinary Prism source, versioned with the package, and a conversion is a pure function of the instant, the zone value, and the package root.

The table is a curated subset of the IANA database, pinned to the release `tzdata_version()` names: each zone carries its standard offset and, where one is observed, the daylight-saving rule in effect at that release. Offsets are computed rather than stored per instant; a `Dst` rule names its switch days the way legislation does (the second Sunday of March at 02:00 standard time), and the calendar arithmetic turns that into an exact UTC instant for any year from 1970 through 9999.

```prism
import Time (..)

import Tzdb (..)

fn main() =
  let noon = wall_of_nanos(1782907200 * 1000000000)
  println(format_in_zone(noon, america_new_york()))
  println(format_in_zone(noon, asia_tokyo()))
```

Historical transitions predating the current rules, and the full zone census, are deliberately out of scope: a program that needs either needs the real database, not a frozen copy of it.
