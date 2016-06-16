import { COMPLETE_GIVEN_ENTRY } from '../actions'

const GivenEntryComplete = (state=false, action) => {
  
  switch (action.type) {
    case COMPLETE_GIVEN_ENTRY:
      return true
    default:
      return state
  }
}

export default GivenEntryComplete

