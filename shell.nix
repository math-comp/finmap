{withEmacs ? false,
 nixpkgs ? (fetchTarball {
  url = "https://github.com/NixOS/nixpkgs/archive/05f0934825c2a0750d4888c4735f9420c906b388.tar.gz";
  sha256 = "1g8c2w0661qn89ajp44znmwfmghbbiygvdzq0rzlvlpdiz28v6gy";
}),
coq-version ? "8.10",
mc ? "1.10.0",
print-env ? false
}:
let
  config.packageOverrides = pkgs:
    with pkgs; rec {
      coqPackages =
        let coqPackages = (with pkgs; {
              "8.7" = coqPackages_8_7;
              "8.8" = coqPackages_8_8;
              "8.9" = coqPackages_8_9;
              "8.10" = coqPackages_8_10;
          }."${coq-version}");
        in
        coqPackages.overrideScope' (self: super: {
          mathcompPkgs = if builtins.isString mc then (super.mathcompGen mc)
                         else super.mathcomp.mathcompGen (o: {
                            version = "dev";
                            name = "coq${self.coq.coq-version}-mathcomp-custom";
                            src = mc;
             });
           mathcomp = self.mathcompPkgs.all;
           mathcomp-ssreflect = self.mathcompPkgs.ssreflect;
       });
       coq = coqPackages.coq;
    };
in
with import nixpkgs {inherit config;};
let
  pgEmacs = emacsWithPackages (epkgs:
    with epkgs.melpaStablePackages; [proof-general]);
in
stdenv.mkDerivation rec {
  name = "env";
  env = buildEnv { name = name; paths = buildInputs; };
  buildInputs = [ coq ] ++ (with coqPackages; [mathcomp-ssreflect])
                ++ lib.optional withEmacs pgEmacs;
  shellHook = ''
    nixEnv (){
      echo "Here is your work environement:"
      for x in $buildInputs; do printf "  "; echo $x | cut -d "-" -f "2-"; done
      echo "you can pass option '--argstr coq-version \"x.y\"' to nix-shell to change coq versions"
    }
  '' + lib.optionalString print-env "nixEnv";
}
