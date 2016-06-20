import { COMPLETE_GIVEN_ENTRY, RECEIVE_FUNCTION_VALIDITY } from '../actions'

const GivenEntryComplete = (state=false, action) => {
  
  switch (action.type) {
    case COMPLETE_GIVEN_ENTRY:
      return true

    case RECEIVE_FUNCTION_VALIDITY:
      return action.valid

    default:
      return state
  }
}

export default GivenEntryComplete

