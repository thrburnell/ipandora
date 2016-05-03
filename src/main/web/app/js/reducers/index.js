import { combineReducers } from 'redux'
import knownFormulas from './knownformulas'
import givens from './givens'
import toShows from './toshows'
import proofSteps from './proofsteps'
import proofStepState from './proofstepstate'
import proofStepJustification from './proofstepjustification'

const ipandoraApp = combineReducers({
  knownFormulas,
  givens,
  toShows,
  proofSteps,
  proofStepState,
  proofStepJustification
})

export default ipandoraApp

