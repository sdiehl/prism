import 'just/development.just'
import 'just/checks.just'
import 'just/docs.just'
import 'just/release.just'

[default]
[private]
default:
    @just --justfile "{{ justfile() }}" --list
