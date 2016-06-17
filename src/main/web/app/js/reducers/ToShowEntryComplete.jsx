import { COMPLETE_TO_SHOW_ENTRY } from '../actions'

const ToShowEntryComplete = (state=false, action) => {
  
  switch (action.type) {
    case COMPLETE_TO_SHOW_ENTRY:
      return true
    default:
      return state
  }
}

export default ToShowEntryComplete

