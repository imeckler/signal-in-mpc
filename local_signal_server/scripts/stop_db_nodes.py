#!/usr/bin/env python3
"""stop_db_nodes.py DIR: stop the database nodes and the Postgres instance that
start_db_nodes.py started in DIR. The directory (config, databases, logs) is left in place."""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import start_db_nodes

if __name__ == '__main__':
    if len(sys.argv) != 2:
        sys.exit(__doc__)
    start_db_nodes.stop(sys.argv[1])
