include "../../lib/util/types.s.dfy"

module test {
  import opened types_s
  datatype Test = test(t : uint64)

module test1 {
  import opened types_s
  datatype Test1 = test1(t : uint64)
}

 test1
class TestIt {
  var testit : test1.Test1;
}

}
