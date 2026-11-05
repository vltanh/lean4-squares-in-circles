"""Complete discovery covers with checked relative-support chord rows."""
from types import SimpleNamespace
import b_relative_support_chord_runtime as RT
import resume_b_five_proxy_round_adaptive_lazy_tree as DRIVER
E=RT.E;OLD=DRIVER.SPLIT.split_choice
def choose(state,point,record):
    ordinary=OLD(state,point,record)
    choices=state['choices']
    if sum(kind=='proxy'for pair,kind,ch in choices)>=5 and not any(kind=='sat'for pair,kind,ch in choices):
        candidates=[(score,pair)for score,pair in E.best_pairs(state,point,36)if 7 in pair or 8 in pair]
        if candidates and candidates[0][0]<-0.08:
            score,pair=candidates[0]
            return dict(kind='sat',pair=list(pair),discovery_extra_cavity_priority=True,physical_sat_violation=score)
    return ordinary
DRIVER.RT=RT;DRIVER.E=E
DRIVER.SPLIT=SimpleNamespace(split_choice=choose,__file__=__file__)
if __name__=='__main__':DRIVER.main()
