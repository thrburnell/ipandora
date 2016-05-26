const toShows = (state = [], action) => {
  switch (action.type) {
    case 'ADD_TO_SHOW':
      return [
        ...state,
        {
          id: action.id,
          uiId: action.uiId,
          formula: action.formula
        }
      ]

    case 'CLEAR_PROOF':
      return []

    default:
      return state
  }
}

export default toShows

