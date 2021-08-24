# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

## [0.3.0] - 2021-08-24

### Changed
- Switched direction of memory block consumption
- Scope can allocate more memory than requested due to alignment

## [0.2.1] - 2021-08-22

### Added
- Methods to move closure returns to scope

## [0.2.0] - 2021-08-20

### Changed
- "nightly" feature renamed to "allocator_api" to reflect rust feature it uses.
- `Arena` type is removed. `Scope` gets methods of the `Arena`.

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