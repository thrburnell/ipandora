import { 
  RECEIVE_INDUCTION_SCHEMA, 
  SAVE_BASE_INITIAL_TERM,
  RECEIVE_BASE_PROOF_STEP_VALIDITY
} from '../actions'

const BaseCase = (state={}, action) => {

  switch (action.type) {
    case RECEIVE_INDUCTION_SCHEMA:
      return action.baseCase
    
    case SAVE_BASE_INITIAL_TERM:
        return {
          ...state,
          steps: [
            {
              term: action.term,
              justification: "INITIAL_STEP"
            }
          ]
        }

    case RECEIVE_BASE_PROOF_STEP_VALIDITY:
        if (action.valid) {
          return {
            ...state,
            stateValid: true,
            steps: [
              ...state.steps,
              {
                term: action.term,
                justification: action.justification
              }
            ]
          }
        } else {
          return {
            ...state,
            stateValid: false
          }
        }

    default:
      return state
  }

}

export default BaseCase

