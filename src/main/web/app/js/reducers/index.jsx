import { combineReducers } from 'redux'
import {reducer as formReducer} from 'redux-form';
import { SAVE_GIVEN_INDEX } from '../actions'
import mode from './Mode'
import toShow from './ToShow'
import toShowEntryComplete from './ToShowEntryComplete'
import given from './Given'
import givenEntryComplete from './GivenEntryComplete'
import baseCase from './BaseCase'
import inductiveCase from './InductiveCase'
import proof from './Proof'
import proofStepType from './ProofStepType'
import proofComplete from './ProofComplete'
import selectedLines from './SelectedLines'
import arbitrary from './Arbitrary'

const ipandoraApp = combineReducers({
  mode,
  
  toShow,
  toShowEntryComplete,
  
  given,
  givenEntryComplete,

  baseCase,
  inductiveCase,
  
  proof,
  proofStepType,
  proofComplete,

  selectedLines,
  arbitrary,
  
  form: formReducer
})

export default ipandoraApp

