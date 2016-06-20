import { combineReducers } from 'redux'
import {reducer as formReducer} from 'redux-form';
import { SAVE_GIVEN_INDEX } from '../actions'
import mode from './Mode'
import toShow from './ToShow'
import toShowEntryComplete from './ToShowEntryComplete'
import given from './Given'
import fn from './Fn'
import givenEntryComplete from './GivenEntryComplete'
import baseCase from './BaseCase'
import inductiveCase from './InductiveCase'
import proof from './Proof'
import baseCaseProof from './BaseCaseProof'
import inductiveCaseProof from './InductiveCaseProof'
import proofStepType from './ProofStepType'
import proofComplete from './ProofComplete'
import selectedLines from './SelectedLines'
import arbitrary from './Arbitrary'
import baseCaseProofComplete from './BaseCaseProofComplete'
import baseCaseProofStepType from './BaseCaseProofStepType'
import inductiveCaseProofComplete from './InductiveCaseProofComplete'
import inductiveCaseProofStepType from './InductiveCaseProofStepType'

const ipandoraApp = combineReducers({
  mode,
  
  toShow,
  toShowEntryComplete,
  
  given,
  fn,
  givenEntryComplete,

  baseCase,
  inductiveCase,
  
  proof,
  baseCaseProof,
  inductiveCaseProof,
  proofStepType,
  proofComplete,

  baseCaseProofComplete,
  baseCaseProofStepType,
  inductiveCaseProofComplete,
  inductiveCaseProofStepType,

  selectedLines,
  arbitrary,
  
  form: formReducer
})

export default ipandoraApp

