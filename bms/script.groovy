import de.prob.Main
import de.prob.animator.domainobjects.ClassicalB
import de.prob.scripting.Api
import de.prob.statespace.Trace
import de.prob.statespace.Transition
import de.prob.statespace.StateSpace

def depth = 1

bms.registerMethod("alphaBeta", {
  Trace trace = bms.getTrace()
  StateSpace stateSpace = trace.getStateSpace()
  val = new ClassicalB("value")
  stateSpace.subscribe(this, val)

  def result = alphaBeta(trace, -250, 250, depth, false)
  Trace nTrace = trace.add(result.transition)
  bms.getAnimationSelector().traceChange(nTrace)

  result.value
})

def alphaBeta(Trace trace, alpha, beta, depth, max) {
    Transition transition = trace.currentTransition
    int best
    Transition trans
    List<Transition> transitions = transition.destination.outTransitions
    transitions.removeAll {tr -> tr.name.equals("evalState") || tr.name.startsWith("test_")}
    if (transitions.size() == 0 || depth == 0) {
        def t = trace.execute("evalState")
        best = Integer.parseInt(t.evalCurrent(val) as String)
        trans = transition
        bms.log("Evaluated state with ID " + t.currentState.id + " and value " + best)
    } else {
        if (max) {
            best = alpha
            for (Transition t : transitions) {
                def childResult = alphaBeta(trace.add(t), best, beta, depth-1, false)
                final int childVal = childResult.get("value")
                if (best < childVal) {
                    trans = t
                }
                best = Math.max(best, childVal)
                if (beta <= best) {
                    break
                }
            }
        } else {
            best = beta
            for (Transition t : transitions) {
                def childResult = alphaBeta(trace.add(t), alpha, best, depth-1, true)
                final int childVal = childResult.get("value")
                if (best > childVal) {
                    trans = t
                }
                best = Math.min(best, childVal)
                if (best <= alpha) {
                    break
                }
            }
        }
    }

    ["value": best, "transition": trans.id]
}
