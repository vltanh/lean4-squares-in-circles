"""Independent exact-dyadic replay; does not import or claim to execute Arb."""
import argparse
import sys
import rational_arb_compat as backend


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--log',default='RATIONAL_REPLAY_LOG.md')
    args = parser.parse_args()
    if any(k in sys.modules for k in ('ia','cert_main','cert_scalars')):
        raise RuntimeError('run in a fresh Python process')
    sys.modules['flint'] = backend
    import run_all
    print(backend.__certificate_backend__,flush=True)
    return run_all.main(args.log)


if __name__=='__main__':
    sys.exit(0 if main() else 1)
