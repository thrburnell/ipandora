import { connect } from 'react-redux'
import FormulaInput from '../components/FormulaInput'
import { addGiven } from '../actions'

const mapStateToProps = () => ({})

const mapDispatchToProps = (dispatch) => (
  {
    onEnterPress: (value) => dispatch(addGiven(value))
  }
)

const RAddGiven = connect(
  mapStateToProps,
  mapDispatchToProps
)(FormulaInput)

export default RAddGiven

