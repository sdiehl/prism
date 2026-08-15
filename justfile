import 'just/development.just'
import 'just/checks.just'
import 'just/docs.just'
import 'just/release.just'

# Cap local parallelism: an uncapped release build plus the native oracles can
# exhaust unified memory on a laptop and freeze the machine. CI invokes cargo
# directly with its own profile, so these caps apply only to just recipes.
# Override per invocation, e.g. `PRISM_TEST_THREADS=8 just t`.

export CARGO_BUILD_JOBS := env_var_or_default("PRISM_BUILD_JOBS", "6")
export NEXTEST_TEST_THREADS := env_var_or_default("PRISM_TEST_THREADS", "4")
export RUST_TEST_THREADS := env_var_or_default("PRISM_TEST_THREADS", "4")

[default]
[private]
default:
    @just --justfile "{{ justfile() }}" --list
