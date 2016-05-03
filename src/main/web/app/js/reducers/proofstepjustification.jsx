const proofStepJustification = (state = [], action) => {
  switch (action.type) {
    case 'SELECT_JUSTIFICATION':
      if (state.findIndex(e => e == action.id) < 0) {
        return  [
         ...state,
          action.id
        ]
      }
      return state

    default:
      return state
  }
}

export default proofStepJustification

