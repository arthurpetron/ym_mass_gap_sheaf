#!/usr/bin/env bash

# Shared, start-anchored process patterns for every repository-owned Mac load
# fence.  Match the executable command prefix, not arbitrary later argv text:
# a supervising wrapper whose arguments contain `lake build` must not match
# itself.  The forms below cover direct tools, Python pytest launchers, and the
# official GitHub runner's foreground, update, and service processes on macOS.

readonly YMGAP_HIGH_LOAD_PROCESS_PATTERN='^([^[:space:]]*/)?(lean|lake|pytest|py[.]test)([[:space:]]|$)|^([^[:space:]]*/)?python[0-9.]*([[:space:]]+-[^[:space:]]+)*[[:space:]]+(-m[[:space:]]+pytest|([^[:space:]]*/)?(pytest|py[.]test))([[:space:]]|$)'

readonly YMGAP_RUNNER_PROCESS_PATTERN='^([^[:space:]]*/)?Runner[.](Listener|Worker|PluginHost)([[:space:]]|$)|^([^[:space:]]*/)?(bash|sh)([[:space:]]+-[^[:space:]]+)*[[:space:]]+([^[:space:]]*/)?(run[.]sh|run-helper[.]sh|safe_sleep[.]sh|runsvc[.]sh|svc[.]sh|_update[.]sh|update[.]sh)([[:space:]]|$)|^([^[:space:]]*/)?node[0-9.]*([[:space:]]+-[^[:space:]]+)*[[:space:]]+([^[:space:]]*/)?RunnerService[.]js([[:space:]]|$)'

readonly YMGAP_CONFLICT_PROCESS_PATTERN="${YMGAP_HIGH_LOAD_PROCESS_PATTERN}|${YMGAP_RUNNER_PROCESS_PATTERN}"
