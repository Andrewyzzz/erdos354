"""Redact machine-local paths without changing mathematical diagnostic text.

Published logs must identify this transformation. These substitutions do not
erase paths from earlier Git commits and are not a general secret scanner.
"""
from pathlib import Path
import re

NOTICE = ('LOG FORMAT: public; machine-local paths are replaced by symbolic '
          'locations. Diagnostic text and exit status are retained.\n')


def redact(text, repository=None, dependency_cache=None):
    mappings = []
    if dependency_cache:
        mappings.append((str(dependency_cache), '$DEPENDENCY_CACHE'))
    if repository:
        mappings.append((str(repository), '$REPOSITORY'))
    for original, replacement in sorted(mappings, key=lambda pair: -len(pair[0])):
        text = text.replace(original, replacement)

    def temporary(match):
        path = match.group(0)
        if 'erdos354-lean-clean-' in path and '/formalization' in path:
            return '$FRESH_PROJECT' + path.split('/formalization', 1)[1]
        return '$TEMPORARY/' + Path(path).name

    text = re.sub(r'/(?:private/)?var/folders/[^\s\"\'<>\]\)]+', temporary, text)
    text = re.sub(r'/tmp/[^\s\"\'<>\]\)]+', temporary, text)
    text = re.sub(r'/(?:Users|home)/[^/\s\"\']+/\.elan', '$ELAN_HOME', text)
    text = re.sub(r'/(?:Users|home)/[^\s\"\'<>\]\)]+',
                  lambda match: '$LOCAL_PATH/' + Path(match.group(0)).name, text)
    return text


def publish_log(text, repository=None, dependency_cache=None):
    public = redact(text, repository, dependency_cache)
    return public if public.startswith(NOTICE) else NOTICE + public
