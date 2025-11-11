# Verifiable

> [!WARNING]
>
> *Verifiable* is now **deprecated**.

## Description

*Verifiable* contains all the specifications and verifiable code for the formal
verification. It converts all the syntax that is not suitable for formal verification
into the structures that can be parsed and evaluated by the formal verification tools.

## Usage

To build the Verifiable module, you need to run the following command:

```shell
cargo dv compile --targets <target1> <target2> ...
```

## Example

See the impls of `CursorMut` in `ostd/src/mm/frame/linked_list`. Note that the `CursorMut`
struct itself is now defined in `aster_common/src/page/meta/linked_list`, and its abstract
models are defined in `aster_common/src/page/meta/frame_list_model`. Associated functions have been annotated
with enough information for Verus to accept them, but have no specification.

In `ostd/src/mm/frame/linked_list.rs`, the `CursorMut` impls demonstrate the use of permissioned pointers
and their macros, and have the appropriate `requires` statements that allow Verus to verify their basic behavior.
In the *verified* branch, we will add specifications to these.