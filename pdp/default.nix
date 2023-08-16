{ mkDerivation, aeson, base, binary, kind-integer, kind-rational
, lib, singletons
}:
mkDerivation {
  pname = "pdp";
  version = "0.1.0";
  src = ./.;
  libraryHaskellDepends = [
    aeson base binary kind-integer kind-rational singletons
  ];
  testHaskellDepends = [ base ];
  homepage = "https://github.com/k0001/hs-pdp";
  description = "Phantoms of Departed Proofs. Alternative API for the Ghost of Departed Proofs ideas";
  license = lib.licenses.bsd3;
}
