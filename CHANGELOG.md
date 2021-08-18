# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

## [0.1.1] - 2021-08-19

### Added
- Reset method for scopes
- Ring example

### Fixed
- Debug output

## [0.1.0] - 2021-08-19
### Added
- Re-exports of allocator-api types and traits when "nightly" feature is enabled.
- Copies of allocator-api types and traits when "nightly" feature is disabled
- Arena allocator that allocates with simple increment and deallocates all memory at once on reset
- Scope wrapper for Arena that allows moving value onto scope and drops all values on scope drop. Also frees any memory allocated within the scope.
- Methods to move whole iterators onto scope returning slices.
- Basic usage example.