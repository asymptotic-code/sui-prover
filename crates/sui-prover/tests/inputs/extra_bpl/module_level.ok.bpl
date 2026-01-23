// Custom Boogie procedure for module-level extra_bpl test
procedure {:inline 1} $42_extra_bpl_module_test_custom_multiply(_$t0: int, _$t1: int) returns ($ret0: int) {
    $ret0 := _$t0 * _$t1;
}
