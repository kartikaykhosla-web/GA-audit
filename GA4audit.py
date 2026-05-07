#!/usr/bin/env python3
"""Compatibility wrapper for the current GA4 auditor implementation."""

from GA4audit1 import audit_single_url, create_driver, main

__all__ = ["audit_single_url", "create_driver", "main"]


if __name__ == "__main__":
    main()
